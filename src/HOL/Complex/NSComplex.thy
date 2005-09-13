(*  Title:       NSComplex.thy
    ID:      $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header{*Nonstandard Complex Numbers*}

theory NSComplex
imports Complex
begin

types hcomplex = "complex star"

syntax hcomplex_of_complex :: "real => real star"
translations "hcomplex_of_complex" => "star_of :: complex => complex star"

constdefs

  (*--- real and Imaginary parts ---*)

  hRe :: "hcomplex => hypreal"
  "hRe(z) == ( *f* Re) z"

  hIm :: "hcomplex => hypreal"
  "hIm(z) == ( *f* Im) z"


  (*----------- modulus ------------*)

  hcmod :: "hcomplex => hypreal"
  "hcmod z == ( *f* cmod) z"

  (*------ imaginary unit ----------*)

  iii :: hcomplex
  "iii == star_of ii"

  (*------- complex conjugate ------*)

  hcnj :: "hcomplex => hcomplex"
  "hcnj z == ( *f* cnj) z"

  (*------------ Argand -------------*)

  hsgn :: "hcomplex => hcomplex"
  "hsgn z == ( *f* sgn) z"

  harg :: "hcomplex => hypreal"
  "harg z == ( *f* arg) z"

  (* abbreviation for (cos a + i sin a) *)
  hcis :: "hypreal => hcomplex"
  "hcis a == ( *f* cis) a"

  (*----- injection from hyperreals -----*)

  hcomplex_of_hypreal :: "hypreal => hcomplex"
  "hcomplex_of_hypreal r == ( *f* complex_of_real) r"

  (* abbreviation for r*(cos a + i sin a) *)
  hrcis :: "[hypreal, hypreal] => hcomplex"
(*  "hrcis r a == hcomplex_of_hypreal r * hcis a" *)
  "hrcis r a == Ifun2_of rcis r a"

  (*------------ e ^ (x + iy) ------------*)

  hexpi :: "hcomplex => hcomplex"
(*  "hexpi z == hcomplex_of_hypreal(( *f* exp) (hRe z)) * hcis (hIm z)"*)
  "hexpi z == ( *f* expi) z"

  HComplex :: "[hypreal,hypreal] => hcomplex"
  "HComplex == Ifun2_of Complex"

  hcpow :: "[hcomplex,hypnat] => hcomplex"  (infixr "hcpow" 80)
  "(z::hcomplex) hcpow (n::hypnat) == Ifun2_of (op ^) z n"

lemmas hcomplex_defs [transfer_unfold] =
  hRe_def hIm_def hcmod_def iii_def hcnj_def hsgn_def harg_def hcis_def
  hcomplex_of_hypreal_def hrcis_def hexpi_def HComplex_def hcpow_def


subsection{*Properties of Nonstandard Real and Imaginary Parts*}

lemma hRe: "hRe (star_n X) = star_n (%n. Re(X n))"
by (simp add: hRe_def starfun)

lemma hIm: "hIm (star_n X) = star_n (%n. Im(X n))"
by (simp add: hIm_def starfun)

lemma hcomplex_hRe_hIm_cancel_iff:
     "!!w z. (w=z) = (hRe(w) = hRe(z) & hIm(w) = hIm(z))"
by (transfer, rule complex_Re_Im_cancel_iff)

lemma hcomplex_equality [intro?]: "hRe z = hRe w ==> hIm z = hIm w ==> z = w"
by (simp add: hcomplex_hRe_hIm_cancel_iff)

lemma hcomplex_hRe_zero [simp]: "hRe 0 = 0"
by (simp add: hRe star_n_zero_num)

lemma hcomplex_hIm_zero [simp]: "hIm 0 = 0"
by (simp add: hIm star_n_zero_num)

lemma hcomplex_hRe_one [simp]: "hRe 1 = 1"
by (simp add: hRe star_n_one_num)

lemma hcomplex_hIm_one [simp]: "hIm 1 = 0"
by (simp add: hIm star_n_one_num star_n_zero_num)


subsection{*Addition for Nonstandard Complex Numbers*}

lemma hRe_add: "!!x y. hRe(x + y) = hRe(x) + hRe(y)"
by (transfer, rule complex_Re_add)

lemma hIm_add: "!!x y. hIm(x + y) = hIm(x) + hIm(y)"
by (transfer, rule complex_Im_add)

subsection{*More Minus Laws*}

lemma hRe_minus: "!!z. hRe(-z) = - hRe(z)"
by (transfer, rule complex_Re_minus)

lemma hIm_minus: "!!z. hIm(-z) = - hIm(z)"
by (transfer, rule complex_Im_minus)

lemma hcomplex_add_minus_eq_minus:
      "x + y = (0::hcomplex) ==> x = -y"
apply (drule OrderedGroup.equals_zero_I)
apply (simp add: minus_equation_iff [of x y])
done

lemma hcomplex_i_mult_eq [simp]: "iii * iii = - 1"
by (simp add: iii_def star_of_def star_n_mult star_n_one_num star_n_minus)

lemma hcomplex_i_mult_left [simp]: "iii * (iii * z) = -z"
by (simp add: mult_assoc [symmetric])

lemma hcomplex_i_not_zero [simp]: "iii \<noteq> 0"
by (simp add: iii_def star_of_def star_n_zero_num star_n_eq_iff)


subsection{*More Multiplication Laws*}

lemma hcomplex_mult_minus_one [simp]: "- 1 * (z::hcomplex) = -z"
by simp

lemma hcomplex_mult_minus_one_right [simp]: "(z::hcomplex) * - 1 = -z"
by simp

lemma hcomplex_mult_left_cancel:
     "(c::hcomplex) \<noteq> (0::hcomplex) ==> (c*a=c*b) = (a=b)"
by (simp add: field_mult_cancel_left)

lemma hcomplex_mult_right_cancel:
     "(c::hcomplex) \<noteq> (0::hcomplex) ==> (a*c=b*c) = (a=b)"
by (simp add: Ring_and_Field.field_mult_cancel_right)


subsection{*Subraction and Division*}

lemma hcomplex_diff_eq_eq [simp]: "((x::hcomplex) - y = z) = (x = z + y)"
by (rule OrderedGroup.diff_eq_eq)

lemma hcomplex_add_divide_distrib: "(x+y)/(z::hcomplex) = x/z + y/z"
by (rule Ring_and_Field.add_divide_distrib)


subsection{*Embedding Properties for @{term hcomplex_of_hypreal} Map*}

lemma hcomplex_of_hypreal:
  "hcomplex_of_hypreal (star_n X) = star_n (%n. complex_of_real (X n))"
by (simp add: hcomplex_of_hypreal_def starfun)

lemma hcomplex_of_hypreal_cancel_iff [iff]:
     "!!x y. (hcomplex_of_hypreal x = hcomplex_of_hypreal y) = (x = y)"
by (transfer, simp)

lemma hcomplex_of_hypreal_one [simp]: "hcomplex_of_hypreal 1 = 1"
by (simp add: hcomplex_of_hypreal star_n_one_num)

lemma hcomplex_of_hypreal_zero [simp]: "hcomplex_of_hypreal 0 = 0"
by (simp add: star_n_zero_num hcomplex_of_hypreal)

lemma hcomplex_of_hypreal_minus [simp]:
     "!!x. hcomplex_of_hypreal(-x) = - hcomplex_of_hypreal x"
by (transfer, simp)

lemma hcomplex_of_hypreal_inverse [simp]:
     "!!x. hcomplex_of_hypreal(inverse x) = inverse(hcomplex_of_hypreal x)"
by (transfer, simp)

lemma hcomplex_of_hypreal_add [simp]:
     "!!x y. hcomplex_of_hypreal (x + y) =
      hcomplex_of_hypreal x + hcomplex_of_hypreal y"
by (transfer, simp)

lemma hcomplex_of_hypreal_diff [simp]:
     "!!x y. hcomplex_of_hypreal (x - y) =
      hcomplex_of_hypreal x - hcomplex_of_hypreal y "
by (transfer, simp)

lemma hcomplex_of_hypreal_mult [simp]:
     "!!x y. hcomplex_of_hypreal (x * y) =
      hcomplex_of_hypreal x * hcomplex_of_hypreal y"
by (transfer, simp)

lemma hcomplex_of_hypreal_divide [simp]:
     "!!x y. hcomplex_of_hypreal(x/y) =
      hcomplex_of_hypreal x / hcomplex_of_hypreal y"
by (transfer, simp)

lemma hRe_hcomplex_of_hypreal [simp]: "!!z. hRe(hcomplex_of_hypreal z) = z"
by (transfer, simp)

lemma hIm_hcomplex_of_hypreal [simp]: "!!z. hIm(hcomplex_of_hypreal z) = 0"
by (transfer, simp)

lemma hcomplex_of_hypreal_epsilon_not_zero [simp]:
     "hcomplex_of_hypreal epsilon \<noteq> 0"
by (simp add: hcomplex_of_hypreal epsilon_def star_n_zero_num star_n_eq_iff)


subsection{*HComplex theorems*}

lemma hRe_HComplex [simp]: "!!x y. hRe (HComplex x y) = x"
by (transfer, simp)

lemma hIm_HComplex [simp]: "!!x y. hIm (HComplex x y) = y"
by (transfer, simp)

text{*Relates the two nonstandard constructions*}
lemma HComplex_eq_Abs_star_Complex:
     "HComplex (star_n X) (star_n Y) =
      star_n (%n::nat. Complex (X n) (Y n))"
by (simp add: hcomplex_hRe_hIm_cancel_iff hRe hIm)

lemma hcomplex_surj [simp]: "HComplex (hRe z) (hIm z) = z"
by (simp add: hcomplex_equality)

lemma hcomplex_induct [case_names rect(*, induct type: hcomplex*)]:
     "(\<And>x y. P (HComplex x y)) ==> P z"
by (rule hcomplex_surj [THEN subst], blast)


subsection{*Modulus (Absolute Value) of Nonstandard Complex Number*}

lemma hcmod: "hcmod (star_n X) = star_n (%n. cmod (X n))"
by (simp add: hcmod_def starfun)

lemma hcmod_zero [simp]: "hcmod(0) = 0"
by (simp add: star_n_zero_num hcmod)

lemma hcmod_one [simp]: "hcmod(1) = 1"
by (simp add: hcmod star_n_one_num)

lemma hcmod_hcomplex_of_hypreal [simp]:
  "!!x. hcmod(hcomplex_of_hypreal x) = abs x"
by (transfer, simp)

lemma hcomplex_of_hypreal_abs:
     "hcomplex_of_hypreal (abs x) =
      hcomplex_of_hypreal(hcmod(hcomplex_of_hypreal x))"
by simp

lemma HComplex_inject [simp]:
  "!!x y x' y'. HComplex x y = HComplex x' y' = (x=x' & y=y')"
by (transfer, simp)

lemma HComplex_add [simp]:
  "!!x1 y1 x2 y2. HComplex x1 y1 + HComplex x2 y2 = HComplex (x1+x2) (y1+y2)"
by (transfer, simp)

lemma HComplex_minus [simp]: "!!x y. - HComplex x y = HComplex (-x) (-y)"
by (transfer, simp)

lemma HComplex_diff [simp]:
  "!!x1 y1 x2 y2. HComplex x1 y1 - HComplex x2 y2 = HComplex (x1-x2) (y1-y2)"
by (transfer, rule complex_diff)

lemma HComplex_mult [simp]:
  "!!x1 y1 x2 y2. HComplex x1 y1 * HComplex x2 y2 =
   HComplex (x1*x2 - y1*y2) (x1*y2 + y1*x2)"
by (transfer, rule complex_mult)

(*HComplex_inverse is proved below*)

lemma hcomplex_of_hypreal_eq: "!!r. hcomplex_of_hypreal r = HComplex r 0"
apply (transfer)
apply (simp add: complex_of_real_def)
done

lemma HComplex_add_hcomplex_of_hypreal [simp]:
     "HComplex x y + hcomplex_of_hypreal r = HComplex (x+r) y"
by (simp add: hcomplex_of_hypreal_eq)

lemma hcomplex_of_hypreal_add_HComplex [simp]:
     "hcomplex_of_hypreal r + HComplex x y = HComplex (r+x) y"
by (simp add: i_def hcomplex_of_hypreal_eq)

lemma HComplex_mult_hcomplex_of_hypreal:
     "HComplex x y * hcomplex_of_hypreal r = HComplex (x*r) (y*r)"
by (simp add: hcomplex_of_hypreal_eq)

lemma hcomplex_of_hypreal_mult_HComplex:
     "hcomplex_of_hypreal r * HComplex x y = HComplex (r*x) (r*y)"
by (simp add: i_def hcomplex_of_hypreal_eq)

lemma i_hcomplex_of_hypreal [simp]:
     "!!r. iii * hcomplex_of_hypreal r = HComplex 0 r"
by (transfer, rule i_complex_of_real)

lemma hcomplex_of_hypreal_i [simp]:
     "!!r. hcomplex_of_hypreal r * iii = HComplex 0 r"
by (transfer, rule complex_of_real_i)


subsection{*Conjugation*}

lemma hcnj: "hcnj (star_n X) = star_n (%n. cnj(X n))"
by (simp add: hcnj_def starfun)

lemma hcomplex_hcnj_cancel_iff [iff]: "!!x y. (hcnj x = hcnj y) = (x = y)"
by (transfer, rule complex_cnj_cancel_iff)

lemma hcomplex_hcnj_hcnj [simp]: "!!z. hcnj (hcnj z) = z"
by (transfer, rule complex_cnj_cnj)

lemma hcomplex_hcnj_hcomplex_of_hypreal [simp]:
     "!!x. hcnj (hcomplex_of_hypreal x) = hcomplex_of_hypreal x"
by (transfer, rule complex_cnj_complex_of_real)

lemma hcomplex_hmod_hcnj [simp]: "!!z. hcmod (hcnj z) = hcmod z"
by (transfer, rule complex_mod_cnj)

lemma hcomplex_hcnj_minus: "!!z. hcnj (-z) = - hcnj z"
by (transfer, rule complex_cnj_minus)

lemma hcomplex_hcnj_inverse: "!!z. hcnj(inverse z) = inverse(hcnj z)"
by (transfer, rule complex_cnj_inverse)

lemma hcomplex_hcnj_add: "!!w z. hcnj(w + z) = hcnj(w) + hcnj(z)"
by (transfer, rule complex_cnj_add)

lemma hcomplex_hcnj_diff: "!!w z. hcnj(w - z) = hcnj(w) - hcnj(z)"
by (transfer, rule complex_cnj_diff)

lemma hcomplex_hcnj_mult: "!!w z. hcnj(w * z) = hcnj(w) * hcnj(z)"
by (transfer, rule complex_cnj_mult)

lemma hcomplex_hcnj_divide: "!!w z. hcnj(w / z) = (hcnj w)/(hcnj z)"
by (transfer, rule complex_cnj_divide)

lemma hcnj_one [simp]: "hcnj 1 = 1"
by (transfer, rule complex_cnj_one)

lemma hcomplex_hcnj_zero [simp]: "hcnj 0 = 0"
by (transfer, rule complex_cnj_zero)

lemma hcomplex_hcnj_zero_iff [iff]: "!!z. (hcnj z = 0) = (z = 0)"
by (transfer, rule complex_cnj_zero_iff)

lemma hcomplex_mult_hcnj:
     "!!z. z * hcnj z = hcomplex_of_hypreal (hRe(z) ^ 2 + hIm(z) ^ 2)"
by (transfer, rule complex_mult_cnj)


subsection{*More Theorems about the Function @{term hcmod}*}

lemma hcomplex_hcmod_eq_zero_cancel [simp]: "!!x. (hcmod x = 0) = (x = 0)"
by (transfer, rule complex_mod_eq_zero_cancel)

lemma hcmod_hcomplex_of_hypreal_of_nat [simp]:
     "hcmod (hcomplex_of_hypreal(hypreal_of_nat n)) = hypreal_of_nat n"
by (simp add: abs_if linorder_not_less)

lemma hcmod_hcomplex_of_hypreal_of_hypnat [simp]:
     "hcmod (hcomplex_of_hypreal(hypreal_of_hypnat n)) = hypreal_of_hypnat n"
by (simp add: abs_if linorder_not_less)

lemma hcmod_minus [simp]: "!!x. hcmod (-x) = hcmod(x)"
by (transfer, rule complex_mod_minus)

lemma hcmod_mult_hcnj: "!!z. hcmod(z * hcnj(z)) = hcmod(z) ^ 2"
by (transfer, rule complex_mod_mult_cnj)

lemma hcmod_ge_zero [simp]: "!!x. (0::hypreal) \<le> hcmod x"
by (transfer, rule complex_mod_ge_zero)

lemma hrabs_hcmod_cancel [simp]: "abs(hcmod x) = hcmod x"
by (simp add: abs_if linorder_not_less)

lemma hcmod_mult: "!!x y. hcmod(x*y) = hcmod(x) * hcmod(y)"
by (transfer, rule complex_mod_mult)

lemma hcmod_add_squared_eq:
  "!!x y. hcmod(x + y) ^ 2 = hcmod(x) ^ 2 + hcmod(y) ^ 2 + 2 * hRe(x * hcnj y)"
by (transfer, rule complex_mod_add_squared_eq)

lemma hcomplex_hRe_mult_hcnj_le_hcmod [simp]:
  "!!x y. hRe(x * hcnj y) \<le> hcmod(x * hcnj y)"
by (transfer, simp)

lemma hcomplex_hRe_mult_hcnj_le_hcmod2 [simp]:
  "!!x y. hRe(x * hcnj y) \<le> hcmod(x * y)"
by (transfer, simp)

lemma hcmod_triangle_squared [simp]:
  "!!x y. hcmod (x + y) ^ 2 \<le> (hcmod(x) + hcmod(y)) ^ 2"
by (transfer, simp)

lemma hcmod_triangle_ineq [simp]:
  "!!x y. hcmod (x + y) \<le> hcmod(x) + hcmod(y)"
by (transfer, simp)

lemma hcmod_triangle_ineq2 [simp]:
  "!!a b. hcmod(b + a) - hcmod b \<le> hcmod a"
by (transfer, simp)

lemma hcmod_diff_commute: "!!x y. hcmod (x - y) = hcmod (y - x)"
by (transfer, rule complex_mod_diff_commute)

lemma hcmod_add_less:
  "!!x y r s. [| hcmod x < r; hcmod y < s |] ==> hcmod (x + y) < r + s"
by (transfer, rule complex_mod_add_less)

lemma hcmod_mult_less:
  "!!x y r s. [| hcmod x < r; hcmod y < s |] ==> hcmod (x * y) < r * s"
by (transfer, rule complex_mod_mult_less)

lemma hcmod_diff_ineq [simp]: "!!a b. hcmod(a) - hcmod(b) \<le> hcmod(a + b)"
by (transfer, simp)


subsection{*A Few Nonlinear Theorems*}

lemma hcpow: "star_n X hcpow star_n Y = star_n (%n. X n ^ Y n)"
by (simp add: hcpow_def Ifun2_of_def star_of_def Ifun_star_n)

lemma hcomplex_of_hypreal_hyperpow:
     "!!x n. hcomplex_of_hypreal (x pow n) = (hcomplex_of_hypreal x) hcpow n"
by (transfer, rule complex_of_real_pow)

lemma hcmod_hcpow: "!!x n. hcmod(x hcpow n) = hcmod(x) pow n"
by (transfer, rule complex_mod_complexpow)

lemma hcmod_hcomplex_inverse: "!!x. hcmod(inverse x) = inverse(hcmod x)"
by (transfer, rule complex_mod_inverse)

lemma hcmod_divide: "hcmod(x/y) = hcmod(x)/(hcmod y)"
by (simp add: divide_inverse hcmod_mult hcmod_hcomplex_inverse)


subsection{*Exponentiation*}

lemma hcomplexpow_0 [simp]:   "z ^ 0       = (1::hcomplex)"
by (rule power_0)

lemma hcomplexpow_Suc [simp]: "z ^ (Suc n) = (z::hcomplex) * (z ^ n)"
by (rule power_Suc)

lemma hcomplexpow_i_squared [simp]: "iii ^ 2 = - 1"
by (simp add: power2_eq_square)


lemma hcomplex_of_hypreal_pow:
     "hcomplex_of_hypreal (x ^ n) = (hcomplex_of_hypreal x) ^ n"
apply (induct_tac "n")
apply (auto simp add: hcomplex_of_hypreal_mult [symmetric])
done

lemma hcomplex_hcnj_pow: "hcnj(z ^ n) = hcnj(z) ^ n"
apply (induct_tac "n")
apply (auto simp add: hcomplex_hcnj_mult)
done

lemma hcmod_hcomplexpow: "hcmod(x ^ n) = hcmod(x) ^ n"
apply (induct_tac "n")
apply (auto simp add: hcmod_mult)
done

lemma hcpow_minus:
     "!!x n. (-x::hcomplex) hcpow n =
      (if ( *p* even) n then (x hcpow n) else -(x hcpow n))"
by (transfer, rule neg_power_if)

lemma hcpow_mult:
  "!!r s n. ((r::hcomplex) * s) hcpow n = (r hcpow n) * (s hcpow n)"
by (transfer, rule power_mult_distrib)

lemma hcpow_zero [simp]: "!!n. 0 hcpow (n + 1) = 0"
by (transfer, simp)

lemma hcpow_zero2 [simp]: "0 hcpow (hSuc n) = 0"
by (simp add: hSuc_def)

lemma hcpow_not_zero [simp,intro]:
  "!!r n. r \<noteq> 0 ==> r hcpow n \<noteq> (0::hcomplex)"
by (transfer, simp)

lemma hcpow_zero_zero: "r hcpow n = (0::hcomplex) ==> r = 0"
by (blast intro: ccontr dest: hcpow_not_zero)

lemma star_n_divide: "star_n X / star_n Y = star_n (%n. X n / Y n)"
by (simp add: star_divide_def Ifun2_of_def star_of_def Ifun_star_n)

subsection{*The Function @{term hsgn}*}

lemma hsgn: "hsgn (star_n X) = star_n (%n. sgn (X n))"
by (simp add: hsgn_def starfun)

lemma hsgn_zero [simp]: "hsgn 0 = 0"
by (simp add: star_n_zero_num hsgn)

lemma hsgn_one [simp]: "hsgn 1 = 1"
by (simp add: star_n_one_num hsgn)

lemma hsgn_minus: "!!z. hsgn (-z) = - hsgn(z)"
by (transfer, rule sgn_minus)

lemma hsgn_eq: "!!z. hsgn z = z / hcomplex_of_hypreal (hcmod z)"
by (transfer, rule sgn_eq)

lemma hcmod_i: "!!x y. hcmod (HComplex x y) = ( *f* sqrt) (x ^ 2 + y ^ 2)"
by (transfer, rule complex_mod)

lemma hcomplex_eq_cancel_iff1 [simp]:
     "(hcomplex_of_hypreal xa = HComplex x y) = (xa = x & y = 0)"
by (simp add: hcomplex_of_hypreal_eq)

lemma hcomplex_eq_cancel_iff2 [simp]:
     "(HComplex x y = hcomplex_of_hypreal xa) = (x = xa & y = 0)"
by (simp add: hcomplex_of_hypreal_eq)

lemma HComplex_eq_0 [simp]: "(HComplex x y = 0) = (x = 0 & y = 0)"
by (insert hcomplex_eq_cancel_iff2 [of _ _ 0], simp)

lemma HComplex_eq_1 [simp]: "(HComplex x y = 1) = (x = 1 & y = 0)"
by (insert hcomplex_eq_cancel_iff2 [of _ _ 1], simp)

lemma i_eq_HComplex_0_1: "iii = HComplex 0 1"
by (insert hcomplex_of_hypreal_i [of 1], simp)

lemma HComplex_eq_i [simp]: "(HComplex x y = iii) = (x = 0 & y = 1)"
by (simp add: i_eq_HComplex_0_1) 

lemma hRe_hsgn [simp]: "!!z. hRe(hsgn z) = hRe(z)/hcmod z"
by (transfer, simp)

lemma hIm_hsgn [simp]: "!!z. hIm(hsgn z) = hIm(z)/hcmod z"
by (transfer, simp)

(*????move to RealDef????*)
lemma real_two_squares_add_zero_iff [simp]: "(x*x + y*y = 0) = ((x::real) = 0 & y = 0)"
by (auto intro: real_sum_squares_cancel iff: real_add_eq_0_iff)

lemma hcomplex_inverse_complex_split:
     "!!x y. inverse(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y) =
      hcomplex_of_hypreal(x/(x ^ 2 + y ^ 2)) -
      iii * hcomplex_of_hypreal(y/(x ^ 2 + y ^ 2))"
by (transfer, rule complex_inverse_complex_split)

lemma HComplex_inverse:
     "!!x y. inverse (HComplex x y) =
      HComplex (x/(x ^ 2 + y ^ 2)) (-y/(x ^ 2 + y ^ 2))"
by (transfer, rule complex_inverse)

lemma hRe_mult_i_eq[simp]:
    "!!y. hRe (iii * hcomplex_of_hypreal y) = 0"
by (transfer, simp)

lemma hIm_mult_i_eq [simp]:
    "!!y. hIm (iii * hcomplex_of_hypreal y) = y"
by (transfer, simp)

lemma hcmod_mult_i [simp]: "!!y. hcmod (iii * hcomplex_of_hypreal y) = abs y"
by (transfer, simp)

lemma hcmod_mult_i2 [simp]: "hcmod (hcomplex_of_hypreal y * iii) = abs y"
by (simp only: hcmod_mult_i mult_commute)

(*---------------------------------------------------------------------------*)
(*  harg                                                                     *)
(*---------------------------------------------------------------------------*)

lemma harg: "harg (star_n X) = star_n (%n. arg (X n))"
by (simp add: harg_def starfun)

lemma cos_harg_i_mult_zero_pos:
     "!!y. 0 < y ==> ( *f* cos) (harg(HComplex 0 y)) = 0"
by (transfer, rule cos_arg_i_mult_zero_pos)

lemma cos_harg_i_mult_zero_neg:
     "!!y. y < 0 ==> ( *f* cos) (harg(HComplex 0 y)) = 0"
by (transfer, rule cos_arg_i_mult_zero_neg)

lemma cos_harg_i_mult_zero [simp]:
     "y \<noteq> 0 ==> ( *f* cos) (harg(HComplex 0 y)) = 0"
by (auto simp add: linorder_neq_iff
                   cos_harg_i_mult_zero_pos cos_harg_i_mult_zero_neg)

lemma hcomplex_of_hypreal_zero_iff [simp]:
     "!!y. (hcomplex_of_hypreal y = 0) = (y = 0)"
by (transfer, simp)


subsection{*Polar Form for Nonstandard Complex Numbers*}

lemma complex_split_polar2:
     "\<forall>n. \<exists>r a. (z n) =  complex_of_real r * (Complex (cos a) (sin a))"
by (blast intro: complex_split_polar)

lemma lemma_hypreal_P_EX2:
     "(\<exists>(x::hypreal) y. P x y) =
      (\<exists>f g. P (star_n f) (star_n g))"
apply auto
apply (rule_tac x = x in star_cases)
apply (rule_tac x = y in star_cases, auto)
done

lemma hcomplex_split_polar:
  "!!z. \<exists>r a. z = hcomplex_of_hypreal r * (HComplex(( *f* cos) a)(( *f* sin) a))"
by (transfer, rule complex_split_polar)

lemma hcis: "hcis (star_n X) = star_n (%n. cis (X n))"
by (simp add: hcis_def starfun)

lemma hcis_eq:
   "!!a. hcis a =
    (hcomplex_of_hypreal(( *f* cos) a) +
    iii * hcomplex_of_hypreal(( *f* sin) a))"
by (transfer, simp add: cis_def)

lemma hrcis: "hrcis (star_n X) (star_n Y) = star_n (%n. rcis (X n) (Y n))"
by (simp add: hrcis_def Ifun2_of_def star_of_def Ifun_star_n)

lemma hrcis_Ex: "!!z. \<exists>r a. z = hrcis r a"
by (transfer, rule rcis_Ex)

lemma hRe_hcomplex_polar [simp]:
     "hRe (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = 
      r * ( *f* cos) a"
by (simp add: hcomplex_of_hypreal_mult_HComplex)

lemma hRe_hrcis [simp]: "!!r a. hRe(hrcis r a) = r * ( *f* cos) a"
by (transfer, rule Re_rcis)

lemma hIm_hcomplex_polar [simp]:
     "hIm (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = 
      r * ( *f* sin) a"
by (simp add: hcomplex_of_hypreal_mult_HComplex)

lemma hIm_hrcis [simp]: "!!r a. hIm(hrcis r a) = r * ( *f* sin) a"
by (transfer, rule Im_rcis)


lemma hcmod_unit_one [simp]:
     "!!a. hcmod (HComplex (( *f* cos) a) (( *f* sin) a)) = 1"
by (transfer, simp)

lemma hcmod_complex_polar [simp]:
     "hcmod (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) =
      abs r"
by (simp only: hcmod_mult hcmod_unit_one, simp)

lemma hcmod_hrcis [simp]: "!!r a. hcmod(hrcis r a) = abs r"
by (transfer, rule complex_mod_rcis)

(*---------------------------------------------------------------------------*)
(*  (r1 * hrcis a) * (r2 * hrcis b) = r1 * r2 * hrcis (a + b)                *)
(*---------------------------------------------------------------------------*)

lemma hcis_hrcis_eq: "!!a. hcis a = hrcis 1 a"
by (transfer, rule cis_rcis_eq)
declare hcis_hrcis_eq [symmetric, simp]

lemma hrcis_mult:
  "!!a b r1 r2. hrcis r1 a * hrcis r2 b = hrcis (r1*r2) (a + b)"
by (transfer, rule rcis_mult)

lemma hcis_mult: "!!a b. hcis a * hcis b = hcis (a + b)"
by (transfer, rule cis_mult)

lemma hcis_zero [simp]: "hcis 0 = 1"
by (transfer, rule cis_zero)

lemma hrcis_zero_mod [simp]: "!!a. hrcis 0 a = 0"
by (transfer, rule rcis_zero_mod)

lemma hrcis_zero_arg [simp]: "!!r. hrcis r 0 = hcomplex_of_hypreal r"
by (transfer, rule rcis_zero_arg)

lemma hcomplex_i_mult_minus [simp]: "iii * (iii * x) = - x"
by (simp add: mult_assoc [symmetric])

lemma hcomplex_i_mult_minus2 [simp]: "iii * iii * x = - x"
by simp

lemma hcis_hypreal_of_nat_Suc_mult:
   "!!a. hcis (hypreal_of_nat (Suc n) * a) =
     hcis a * hcis (hypreal_of_nat n * a)"
apply (unfold hypreal_of_nat_def)
apply transfer
apply (fold real_of_nat_def)
apply (rule cis_real_of_nat_Suc_mult)
done

lemma NSDeMoivre: "(hcis a) ^ n = hcis (hypreal_of_nat n * a)"
apply (induct_tac "n")
apply (simp_all add: hcis_hypreal_of_nat_Suc_mult)
done

lemma hcis_hypreal_of_hypnat_Suc_mult:
     "!! a n. hcis (hypreal_of_hypnat (n + 1) * a) =
      hcis a * hcis (hypreal_of_hypnat n * a)"
by (transfer, simp add: cis_real_of_nat_Suc_mult)

lemma NSDeMoivre_ext:
  "!!a n. (hcis a) hcpow n = hcis (hypreal_of_hypnat n * a)"
by (transfer, rule DeMoivre)

lemma NSDeMoivre2:
  "!!a r. (hrcis r a) ^ n = hrcis (r ^ n) (hypreal_of_nat n * a)"
apply (unfold hypreal_of_nat_def)
apply transfer
apply (fold real_of_nat_def)
apply (rule DeMoivre2)
done

lemma DeMoivre2_ext:
  "!! a r n. (hrcis r a) hcpow n = hrcis (r pow n) (hypreal_of_hypnat n * a)"
by (transfer, rule DeMoivre2)

lemma hcis_inverse [simp]: "!!a. inverse(hcis a) = hcis (-a)"
by (transfer, simp)

lemma hrcis_inverse: "!!a r. inverse(hrcis r a) = hrcis (inverse r) (-a)"
by (transfer, simp add: rcis_inverse inverse_eq_divide [symmetric])

lemma hRe_hcis [simp]: "!!a. hRe(hcis a) = ( *f* cos) a"
by (transfer, rule Re_cis)

lemma hIm_hcis [simp]: "!!a. hIm(hcis a) = ( *f* sin) a"
by (transfer, rule Im_cis)

lemma cos_n_hRe_hcis_pow_n: "( *f* cos) (hypreal_of_nat n * a) = hRe(hcis a ^ n)"
by (simp add: NSDeMoivre)

lemma sin_n_hIm_hcis_pow_n: "( *f* sin) (hypreal_of_nat n * a) = hIm(hcis a ^ n)"
by (simp add: NSDeMoivre)

lemma cos_n_hRe_hcis_hcpow_n: "( *f* cos) (hypreal_of_hypnat n * a) = hRe(hcis a hcpow n)"
by (simp add: NSDeMoivre_ext)

lemma sin_n_hIm_hcis_hcpow_n: "( *f* sin) (hypreal_of_hypnat n * a) = hIm(hcis a hcpow n)"
by (simp add: NSDeMoivre_ext)

lemma hexpi_add: "!!a b. hexpi(a + b) = hexpi(a) * hexpi(b)"
by (transfer, rule expi_add)


subsection{*@{term hcomplex_of_complex}: the Injection from
  type @{typ complex} to to @{typ hcomplex}*}

lemma inj_hcomplex_of_complex: "inj(hcomplex_of_complex)"
by (rule inj_onI, simp)

lemma hcomplex_of_complex_i: "iii = hcomplex_of_complex ii"
by (simp add: iii_def)

lemma hRe_hcomplex_of_complex:
   "hRe (hcomplex_of_complex z) = hypreal_of_real (Re z)"
by (transfer, rule refl)

lemma hIm_hcomplex_of_complex:
   "hIm (hcomplex_of_complex z) = hypreal_of_real (Im z)"
by (transfer, rule refl)

lemma hcmod_hcomplex_of_complex:
     "hcmod (hcomplex_of_complex x) = hypreal_of_real (cmod x)"
by (transfer, rule refl)


subsection{*Numerals and Arithmetic*}

lemma hcomplex_number_of_def: "(number_of w :: hcomplex) == of_int (Rep_Bin w)"
by (transfer, rule number_of_eq [THEN eq_reflection])

lemma hcomplex_of_hypreal_eq_hcomplex_of_complex: 
     "hcomplex_of_hypreal (hypreal_of_real x) =  
      hcomplex_of_complex (complex_of_real x)"
by (transfer, rule refl)

lemma hcomplex_hypreal_number_of: 
  "hcomplex_of_complex (number_of w) = hcomplex_of_hypreal(number_of w)"
by (transfer, rule complex_number_of [symmetric])

text{*This theorem is necessary because theorems such as
   @{text iszero_number_of_0} only hold for ordered rings. They cannot
   be generalized to fields in general because they fail for finite fields.
   They work for type complex because the reals can be embedded in them.*}
lemma iszero_hcomplex_number_of [simp]:
     "iszero (number_of w :: hcomplex) = iszero (number_of w :: real)"
by (transfer iszero_def, simp)


(*
Goal "z + hcnj z =  
      hcomplex_of_hypreal (2 * hRe(z))"
by (res_inst_tac [("z","z")] eq_Abs_star 1);
by (auto_tac (claset(),HOL_ss addsimps [hRe,hcnj,star_n_add,
    hypreal_mult,hcomplex_of_hypreal,complex_add_cnj]));
qed "star_n_add_hcnj";

Goal "z - hcnj z = \
\     hcomplex_of_hypreal (hypreal_of_real #2 * hIm(z)) * iii";
by (res_inst_tac [("z","z")] eq_Abs_star 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcnj,hcomplex_diff,
    hypreal_of_real_def,hypreal_mult,hcomplex_of_hypreal,
    complex_diff_cnj,iii_def,star_n_mult]));
qed "hcomplex_diff_hcnj";
*)


(*** Real and imaginary stuff ***)

(*Convert???
Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya =  
        number_of xb + iii * number_of yb) =  
   (((number_of xa :: hcomplex) = number_of xb) &  
    ((number_of ya :: hcomplex) = number_of yb))"
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff,
     hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iff";
Addsimps [hcomplex_number_of_eq_cancel_iff];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii = \
\       number_of xb + number_of yb * iii) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iffA,
    hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iffA";
Addsimps [hcomplex_number_of_eq_cancel_iffA];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii = \
\       number_of xb + iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iffB,
    hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iffB";
Addsimps [hcomplex_number_of_eq_cancel_iffB];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\       number_of xb + number_of yb * iii) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iffC,
     hcomplex_hypreal_number_of]));
qed "hcomplex_number_of_eq_cancel_iffC";
Addsimps [hcomplex_number_of_eq_cancel_iffC];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\       number_of xb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff2,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff2";
Addsimps [hcomplex_number_of_eq_cancel_iff2];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii = \
\       number_of xb) = \
\  (((number_of xa :: hcomplex) = number_of xb) & \
\   ((number_of ya :: hcomplex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff2a,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff2a";
Addsimps [hcomplex_number_of_eq_cancel_iff2a];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + iii * number_of ya = \
\    iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = 0) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff3,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff3";
Addsimps [hcomplex_number_of_eq_cancel_iff3];

Goalw [hcomplex_number_of_def] 
  "((number_of xa :: hcomplex) + number_of ya * iii= \
\    iii * number_of yb) = \
\  (((number_of xa :: hcomplex) = 0) & \
\   ((number_of ya :: hcomplex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [hcomplex_eq_cancel_iff3a,
    hcomplex_hypreal_number_of,hcomplex_of_hypreal_zero_iff]));
qed "hcomplex_number_of_eq_cancel_iff3a";
Addsimps [hcomplex_number_of_eq_cancel_iff3a];
*)

lemma hcomplex_number_of_hcnj [simp]:
     "hcnj (number_of v :: hcomplex) = number_of v"
by (transfer, rule complex_number_of_cnj)

lemma hcomplex_number_of_hcmod [simp]: 
      "hcmod(number_of v :: hcomplex) = abs (number_of v :: hypreal)"
by (transfer, rule complex_number_of_cmod)

lemma hcomplex_number_of_hRe [simp]: 
      "hRe(number_of v :: hcomplex) = number_of v"
by (transfer, simp)

lemma hcomplex_number_of_hIm [simp]: 
      "hIm(number_of v :: hcomplex) = 0"
by (transfer, simp)


ML
{*
val iii_def = thm"iii_def";

val hRe = thm"hRe";
val hIm = thm"hIm";
val hcomplex_hRe_hIm_cancel_iff = thm"hcomplex_hRe_hIm_cancel_iff";
val hcomplex_hRe_zero = thm"hcomplex_hRe_zero";
val hcomplex_hIm_zero = thm"hcomplex_hIm_zero";
val hcomplex_hRe_one = thm"hcomplex_hRe_one";
val hcomplex_hIm_one = thm"hcomplex_hIm_one";
val inj_hcomplex_of_complex = thm"inj_hcomplex_of_complex";
val hcomplex_of_complex_i = thm"hcomplex_of_complex_i";
val star_n_add = thm"star_n_add";
val hRe_add = thm"hRe_add";
val hIm_add = thm"hIm_add";
val hRe_minus = thm"hRe_minus";
val hIm_minus = thm"hIm_minus";
val hcomplex_add_minus_eq_minus = thm"hcomplex_add_minus_eq_minus";
val hcomplex_diff_eq_eq = thm"hcomplex_diff_eq_eq";
val hcomplex_mult_minus_one = thm"hcomplex_mult_minus_one";
val hcomplex_mult_minus_one_right = thm"hcomplex_mult_minus_one_right";
val hcomplex_mult_left_cancel = thm"hcomplex_mult_left_cancel";
val hcomplex_mult_right_cancel = thm"hcomplex_mult_right_cancel";
val hcomplex_add_divide_distrib = thm"hcomplex_add_divide_distrib";
val hcomplex_of_hypreal = thm"hcomplex_of_hypreal";
val hcomplex_of_hypreal_cancel_iff = thm"hcomplex_of_hypreal_cancel_iff";
val hcomplex_of_hypreal_minus = thm"hcomplex_of_hypreal_minus";
val hcomplex_of_hypreal_inverse = thm"hcomplex_of_hypreal_inverse";
val hcomplex_of_hypreal_add = thm"hcomplex_of_hypreal_add";
val hcomplex_of_hypreal_diff = thm"hcomplex_of_hypreal_diff";
val hcomplex_of_hypreal_mult = thm"hcomplex_of_hypreal_mult";
val hcomplex_of_hypreal_divide = thm"hcomplex_of_hypreal_divide";
val hcomplex_of_hypreal_one = thm"hcomplex_of_hypreal_one";
val hcomplex_of_hypreal_zero = thm"hcomplex_of_hypreal_zero";
val hcomplex_of_hypreal_pow = thm"hcomplex_of_hypreal_pow";
val hRe_hcomplex_of_hypreal = thm"hRe_hcomplex_of_hypreal";
val hIm_hcomplex_of_hypreal = thm"hIm_hcomplex_of_hypreal";
val hcomplex_of_hypreal_epsilon_not_zero = thm"hcomplex_of_hypreal_epsilon_not_zero";
val hcmod = thm"hcmod";
val hcmod_zero = thm"hcmod_zero";
val hcmod_one = thm"hcmod_one";
val hcmod_hcomplex_of_hypreal = thm"hcmod_hcomplex_of_hypreal";
val hcomplex_of_hypreal_abs = thm"hcomplex_of_hypreal_abs";
val hcnj = thm"hcnj";
val hcomplex_hcnj_cancel_iff = thm"hcomplex_hcnj_cancel_iff";
val hcomplex_hcnj_hcnj = thm"hcomplex_hcnj_hcnj";
val hcomplex_hcnj_hcomplex_of_hypreal = thm"hcomplex_hcnj_hcomplex_of_hypreal";
val hcomplex_hmod_hcnj = thm"hcomplex_hmod_hcnj";
val hcomplex_hcnj_minus = thm"hcomplex_hcnj_minus";
val hcomplex_hcnj_inverse = thm"hcomplex_hcnj_inverse";
val hcomplex_hcnj_add = thm"hcomplex_hcnj_add";
val hcomplex_hcnj_diff = thm"hcomplex_hcnj_diff";
val hcomplex_hcnj_mult = thm"hcomplex_hcnj_mult";
val hcomplex_hcnj_divide = thm"hcomplex_hcnj_divide";
val hcnj_one = thm"hcnj_one";
val hcomplex_hcnj_pow = thm"hcomplex_hcnj_pow";
val hcomplex_hcnj_zero = thm"hcomplex_hcnj_zero";
val hcomplex_hcnj_zero_iff = thm"hcomplex_hcnj_zero_iff";
val hcomplex_mult_hcnj = thm"hcomplex_mult_hcnj";
val hcomplex_hcmod_eq_zero_cancel = thm"hcomplex_hcmod_eq_zero_cancel";

val hcmod_hcomplex_of_hypreal_of_nat = thm"hcmod_hcomplex_of_hypreal_of_nat";
val hcmod_hcomplex_of_hypreal_of_hypnat = thm"hcmod_hcomplex_of_hypreal_of_hypnat";
val hcmod_minus = thm"hcmod_minus";
val hcmod_mult_hcnj = thm"hcmod_mult_hcnj";
val hcmod_ge_zero = thm"hcmod_ge_zero";
val hrabs_hcmod_cancel = thm"hrabs_hcmod_cancel";
val hcmod_mult = thm"hcmod_mult";
val hcmod_add_squared_eq = thm"hcmod_add_squared_eq";
val hcomplex_hRe_mult_hcnj_le_hcmod = thm"hcomplex_hRe_mult_hcnj_le_hcmod";
val hcomplex_hRe_mult_hcnj_le_hcmod2 = thm"hcomplex_hRe_mult_hcnj_le_hcmod2";
val hcmod_triangle_squared = thm"hcmod_triangle_squared";
val hcmod_triangle_ineq = thm"hcmod_triangle_ineq";
val hcmod_triangle_ineq2 = thm"hcmod_triangle_ineq2";
val hcmod_diff_commute = thm"hcmod_diff_commute";
val hcmod_add_less = thm"hcmod_add_less";
val hcmod_mult_less = thm"hcmod_mult_less";
val hcmod_diff_ineq = thm"hcmod_diff_ineq";
val hcpow = thm"hcpow";
val hcomplex_of_hypreal_hyperpow = thm"hcomplex_of_hypreal_hyperpow";
val hcmod_hcomplexpow = thm"hcmod_hcomplexpow";
val hcmod_hcpow = thm"hcmod_hcpow";
val hcpow_minus = thm"hcpow_minus";
val hcmod_hcomplex_inverse = thm"hcmod_hcomplex_inverse";
val hcmod_divide = thm"hcmod_divide";
val hcpow_mult = thm"hcpow_mult";
val hcpow_zero = thm"hcpow_zero";
val hcpow_zero2 = thm"hcpow_zero2";
val hcpow_not_zero = thm"hcpow_not_zero";
val hcpow_zero_zero = thm"hcpow_zero_zero";
val hcomplex_i_mult_eq = thm"hcomplex_i_mult_eq";
val hcomplexpow_i_squared = thm"hcomplexpow_i_squared";
val hcomplex_i_not_zero = thm"hcomplex_i_not_zero";
val star_n_divide = thm"star_n_divide";
val hsgn = thm"hsgn";
val hsgn_zero = thm"hsgn_zero";
val hsgn_one = thm"hsgn_one";
val hsgn_minus = thm"hsgn_minus";
val hsgn_eq = thm"hsgn_eq";
val lemma_hypreal_P_EX2 = thm"lemma_hypreal_P_EX2";
val hcmod_i = thm"hcmod_i";
val hcomplex_eq_cancel_iff2 = thm"hcomplex_eq_cancel_iff2";
val hRe_hsgn = thm"hRe_hsgn";
val hIm_hsgn = thm"hIm_hsgn";
val real_two_squares_add_zero_iff = thm"real_two_squares_add_zero_iff";
val hRe_mult_i_eq = thm"hRe_mult_i_eq";
val hIm_mult_i_eq = thm"hIm_mult_i_eq";
val hcmod_mult_i = thm"hcmod_mult_i";
val hcmod_mult_i2 = thm"hcmod_mult_i2";
val harg = thm"harg";
val cos_harg_i_mult_zero = thm"cos_harg_i_mult_zero";
val hcomplex_of_hypreal_zero_iff = thm"hcomplex_of_hypreal_zero_iff";
val complex_split_polar2 = thm"complex_split_polar2";
val hcomplex_split_polar = thm"hcomplex_split_polar";
val hcis = thm"hcis";
val hcis_eq = thm"hcis_eq";
val hrcis = thm"hrcis";
val hrcis_Ex = thm"hrcis_Ex";
val hRe_hcomplex_polar = thm"hRe_hcomplex_polar";
val hRe_hrcis = thm"hRe_hrcis";
val hIm_hcomplex_polar = thm"hIm_hcomplex_polar";
val hIm_hrcis = thm"hIm_hrcis";
val hcmod_complex_polar = thm"hcmod_complex_polar";
val hcmod_hrcis = thm"hcmod_hrcis";
val hcis_hrcis_eq = thm"hcis_hrcis_eq";
val hrcis_mult = thm"hrcis_mult";
val hcis_mult = thm"hcis_mult";
val hcis_zero = thm"hcis_zero";
val hrcis_zero_mod = thm"hrcis_zero_mod";
val hrcis_zero_arg = thm"hrcis_zero_arg";
val hcomplex_i_mult_minus = thm"hcomplex_i_mult_minus";
val hcomplex_i_mult_minus2 = thm"hcomplex_i_mult_minus2";
val hcis_hypreal_of_nat_Suc_mult = thm"hcis_hypreal_of_nat_Suc_mult";
val NSDeMoivre = thm"NSDeMoivre";
val hcis_hypreal_of_hypnat_Suc_mult = thm"hcis_hypreal_of_hypnat_Suc_mult";
val NSDeMoivre_ext = thm"NSDeMoivre_ext";
val DeMoivre2 = thm"DeMoivre2";
val DeMoivre2_ext = thm"DeMoivre2_ext";
val hcis_inverse = thm"hcis_inverse";
val hrcis_inverse = thm"hrcis_inverse";
val hRe_hcis = thm"hRe_hcis";
val hIm_hcis = thm"hIm_hcis";
val cos_n_hRe_hcis_pow_n = thm"cos_n_hRe_hcis_pow_n";
val sin_n_hIm_hcis_pow_n = thm"sin_n_hIm_hcis_pow_n";
val cos_n_hRe_hcis_hcpow_n = thm"cos_n_hRe_hcis_hcpow_n";
val sin_n_hIm_hcis_hcpow_n = thm"sin_n_hIm_hcis_hcpow_n";
val hexpi_add = thm"hexpi_add";
val hRe_hcomplex_of_complex = thm"hRe_hcomplex_of_complex";
val hIm_hcomplex_of_complex = thm"hIm_hcomplex_of_complex";
val hcmod_hcomplex_of_complex = thm"hcmod_hcomplex_of_complex";
*}

end

(*  Title:       Complex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Description: Complex numbers
*)

theory Complex = HLog:

typedef complex = "{p::(real*real). True}"
  by blast

instance complex :: zero ..
instance complex :: one ..
instance complex :: plus ..
instance complex :: times ..
instance complex :: minus ..
instance complex :: inverse ..
instance complex :: power ..

consts
  "ii"    :: complex        ("ii")

constdefs

  (*--- real and Imaginary parts ---*)

  Re :: "complex => real"
  "Re(z) == fst(Rep_complex z)"

  Im :: "complex => real"
  "Im(z) == snd(Rep_complex z)"

  (*----------- modulus ------------*)

  cmod :: "complex => real"
  "cmod z == sqrt(Re(z) ^ 2 + Im(z) ^ 2)"

  (*----- injection from reals -----*)

  complex_of_real :: "real => complex"
  "complex_of_real r == Abs_complex(r,0::real)"

  (*------- complex conjugate ------*)

  cnj :: "complex => complex"
  "cnj z == Abs_complex(Re z, -Im z)"

  (*------------ Argand -------------*)

  sgn :: "complex => complex"
  "sgn z == z / complex_of_real(cmod z)"

  arg :: "complex => real"
  "arg z == @a. Re(sgn z) = cos a & Im(sgn z) = sin a & -pi < a & a \<le> pi"


defs (overloaded)

  complex_zero_def:
  "0 == Abs_complex(0::real,0)"

  complex_one_def:
  "1 == Abs_complex(1,0::real)"

  (*------ imaginary unit ----------*)

  i_def:
  "ii == Abs_complex(0::real,1)"

  (*----------- negation -----------*)

  complex_minus_def:
  "- (z::complex) == Abs_complex(-Re z, -Im z)"


  (*----------- inverse -----------*)
  complex_inverse_def:
  "inverse (z::complex) == Abs_complex(Re(z)/(Re(z) ^ 2 + Im(z) ^ 2),
                            -Im(z)/(Re(z) ^ 2 + Im(z) ^ 2))"

  complex_add_def:
  "w + (z::complex) == Abs_complex(Re(w) + Re(z),Im(w) + Im(z))"

  complex_diff_def:
  "w - (z::complex) == w + -(z::complex)"

  complex_mult_def:
  "w * (z::complex) == Abs_complex(Re(w) * Re(z) - Im(w) * Im(z),
			Re(w) * Im(z) + Im(w) * Re(z))"


  (*----------- division ----------*)
  complex_divide_def:
  "w / (z::complex) == w * inverse z"


constdefs

  (* abbreviation for (cos a + i sin a) *)
  cis :: "real => complex"
  "cis a == complex_of_real(cos a) + ii * complex_of_real(sin a)"

  (* abbreviation for r*(cos a + i sin a) *)
  rcis :: "[real, real] => complex"
  "rcis r a == complex_of_real r * cis a"

  (* e ^ (x + iy) *)
  expi :: "complex => complex"
  "expi z == complex_of_real(exp (Re z)) * cis (Im z)"


lemma inj_Rep_complex: "inj Rep_complex"
apply (rule inj_on_inverseI)
apply (rule Rep_complex_inverse)
done

lemma inj_Abs_complex: "inj Abs_complex"
apply (rule inj_on_inverseI)
apply (rule Abs_complex_inverse)
apply (simp (no_asm) add: complex_def)
done
declare inj_Abs_complex [THEN injD, simp]

lemma Abs_complex_cancel_iff: "(Abs_complex x = Abs_complex y) = (x = y)"
by (auto dest: inj_Abs_complex [THEN injD])
declare Abs_complex_cancel_iff [simp]

lemma pair_mem_complex: "(x,y) : complex"
by (unfold complex_def, auto)
declare pair_mem_complex [simp]

lemma Abs_complex_inverse2: "Rep_complex (Abs_complex (x,y)) = (x,y)"
apply (simp (no_asm) add: Abs_complex_inverse)
done
declare Abs_complex_inverse2 [simp]

lemma eq_Abs_complex: "(!!x y. z = Abs_complex(x,y) ==> P) ==> P"
apply (rule_tac p = "Rep_complex z" in PairE)
apply (drule_tac f = Abs_complex in arg_cong)
apply (force simp add: Rep_complex_inverse)
done

lemma Re: "Re(Abs_complex(x,y)) = x"
apply (unfold Re_def)
apply (simp (no_asm))
done
declare Re [simp]

lemma Im: "Im(Abs_complex(x,y)) = y"
apply (unfold Im_def)
apply (simp (no_asm))
done
declare Im [simp]

lemma Abs_complex_cancel: "Abs_complex(Re(z),Im(z)) = z"
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp))
done
declare Abs_complex_cancel [simp]

lemma complex_Re_Im_cancel_iff: "(w=z) = (Re(w) = Re(z) & Im(w) = Im(z))"
apply (rule_tac z = w in eq_Abs_complex)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto dest: inj_Abs_complex [THEN injD])
done

lemma complex_Re_zero: "Re 0 = 0"
apply (unfold complex_zero_def)
apply (simp (no_asm))
done

lemma complex_Im_zero: "Im 0 = 0"
apply (unfold complex_zero_def)
apply (simp (no_asm))
done
declare complex_Re_zero [simp] complex_Im_zero [simp]

lemma complex_Re_one: "Re 1 = 1"
apply (unfold complex_one_def)
apply (simp (no_asm))
done
declare complex_Re_one [simp]

lemma complex_Im_one: "Im 1 = 0"
apply (unfold complex_one_def)
apply (simp (no_asm))
done
declare complex_Im_one [simp]

lemma complex_Re_i: "Re(ii) = 0"
by (unfold i_def, auto)
declare complex_Re_i [simp]

lemma complex_Im_i: "Im(ii) = 1"
by (unfold i_def, auto)
declare complex_Im_i [simp]

lemma Re_complex_of_real_zero: "Re(complex_of_real 0) = 0"
apply (unfold complex_of_real_def)
apply (simp (no_asm))
done
declare Re_complex_of_real_zero [simp]

lemma Im_complex_of_real_zero: "Im(complex_of_real 0) = 0"
apply (unfold complex_of_real_def)
apply (simp (no_asm))
done
declare Im_complex_of_real_zero [simp]

lemma Re_complex_of_real_one: "Re(complex_of_real 1) = 1"
apply (unfold complex_of_real_def)
apply (simp (no_asm))
done
declare Re_complex_of_real_one [simp]

lemma Im_complex_of_real_one: "Im(complex_of_real 1) = 0"
apply (unfold complex_of_real_def)
apply (simp (no_asm))
done
declare Im_complex_of_real_one [simp]

lemma Re_complex_of_real: "Re(complex_of_real z) = z"
by (unfold complex_of_real_def, auto)
declare Re_complex_of_real [simp]

lemma Im_complex_of_real: "Im(complex_of_real z) = 0"
by (unfold complex_of_real_def, auto)
declare Im_complex_of_real [simp]


subsection{*Negation*}

lemma complex_minus: "- Abs_complex(x,y) = Abs_complex(-x,-y)"
apply (unfold complex_minus_def)
apply (simp (no_asm))
done

lemma complex_Re_minus: "Re (-z) = - Re z"
apply (unfold Re_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_minus)
done

lemma complex_Im_minus: "Im (-z) = - Im z"
apply (unfold Im_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_minus)
done

lemma complex_minus_minus: "- (- z) = (z::complex)"
apply (unfold complex_minus_def)
apply (simp (no_asm))
done
declare complex_minus_minus [simp]

lemma inj_complex_minus: "inj(%r::complex. -r)"
apply (rule inj_onI)
apply (drule_tac f = uminus in arg_cong, simp)
done

lemma complex_minus_zero: "-(0::complex) = 0"
apply (unfold complex_zero_def)
apply (simp (no_asm) add: complex_minus)
done
declare complex_minus_zero [simp]

lemma complex_minus_zero_iff: "(-x = 0) = (x = (0::complex))"
apply (rule_tac z = x in eq_Abs_complex)
apply (auto dest: inj_Abs_complex [THEN injD]
            simp add: complex_zero_def complex_minus)
done
declare complex_minus_zero_iff [simp]

lemma complex_minus_zero_iff2: "(0 = -x) = (x = (0::real))"
by (auto dest: sym)
declare complex_minus_zero_iff2 [simp]

lemma complex_minus_not_zero_iff: "(-x \<noteq> 0) = (x \<noteq> (0::complex))"
by auto


subsection{*Addition*}

lemma complex_add:
      "Abs_complex(x1,y1) + Abs_complex(x2,y2) = Abs_complex(x1+x2,y1+y2)"
apply (unfold complex_add_def)
apply (simp (no_asm))
done

lemma complex_Re_add: "Re(x + y) = Re(x) + Re(y)"
apply (unfold Re_def)
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_add)
done

lemma complex_Im_add: "Im(x + y) = Im(x) + Im(y)"
apply (unfold Im_def)
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_add)
done

lemma complex_add_commute: "(u::complex) + v = v + u"
apply (unfold complex_add_def)
apply (simp (no_asm) add: real_add_commute)
done

lemma complex_add_assoc: "((u::complex) + v) + w = u + (v + w)"
apply (unfold complex_add_def)
apply (simp (no_asm) add: real_add_assoc)
done

lemma complex_add_left_commute: "(x::complex) + (y + z) = y + (x + z)"
apply (unfold complex_add_def)
apply (simp (no_asm) add: add_left_commute)
done

lemmas complex_add_ac = complex_add_assoc complex_add_commute
                      complex_add_left_commute

lemma complex_add_zero_left: "(0::complex) + z = z"
apply (unfold complex_add_def complex_zero_def)
apply (simp (no_asm))
done
declare complex_add_zero_left [simp]

lemma complex_add_zero_right: "z + (0::complex) = z"
apply (unfold complex_add_def complex_zero_def)
apply (simp (no_asm))
done
declare complex_add_zero_right [simp]

lemma complex_add_minus_right_zero:
      "z + -z = (0::complex)"
apply (unfold complex_add_def complex_minus_def complex_zero_def)
apply (simp (no_asm))
done
declare complex_add_minus_right_zero [simp]

lemma complex_add_minus_left:
      "-z + z = (0::complex)"
apply (unfold complex_add_def complex_minus_def complex_zero_def)
apply (simp (no_asm))
done

lemma complex_add_minus_cancel: "z + (- z + w) = (w::complex)"
apply (simp (no_asm) add: complex_add_assoc [symmetric])
done

lemma complex_minus_add_cancel: "(-z) + (z + w) = (w::complex)"
by (simp add: complex_add_minus_left complex_add_assoc [symmetric])

declare complex_add_minus_cancel [simp] complex_minus_add_cancel [simp]

lemma complex_add_minus_eq_minus: "x + y = (0::complex) ==> x = -y"
by (auto simp add: complex_Re_Im_cancel_iff complex_Re_add complex_Im_add complex_Re_minus complex_Im_minus)

lemma complex_minus_add_distrib: "-(x + y) = -x + -(y::complex)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_minus complex_add)
done
declare complex_minus_add_distrib [simp]

lemma complex_add_left_cancel: "((x::complex) + y = x + z) = (y = z)"
apply safe
apply (drule_tac f = "%t.-x + t" in arg_cong)
apply (simp add: complex_add_minus_left complex_add_assoc [symmetric])
done
declare complex_add_left_cancel [iff]

lemma complex_add_right_cancel: "(y + (x::complex)= z + x) = (y = z)"
apply (simp (no_asm) add: complex_add_commute)
done
declare complex_add_right_cancel [simp]

lemma complex_eq_minus_iff: "((x::complex) = y) = (0 = x + - y)"
apply safe
apply (rule_tac [2] x1 = "-y" in complex_add_right_cancel [THEN iffD1], auto)
done

lemma complex_eq_minus_iff2: "((x::complex) = y) = (x + - y = 0)"
apply safe
apply (rule_tac [2] x1 = "-y" in complex_add_right_cancel [THEN iffD1], auto)
done

lemma complex_diff_0: "(0::complex) - x = -x"
apply (simp (no_asm) add: complex_diff_def)
done

lemma complex_diff_0_right: "x - (0::complex) = x"
apply (simp (no_asm) add: complex_diff_def)
done

lemma complex_diff_self: "x - x = (0::complex)"
apply (simp (no_asm) add: complex_diff_def)
done

declare complex_diff_0 [simp] complex_diff_0_right [simp] complex_diff_self [simp]

lemma complex_diff:
      "Abs_complex(x1,y1) - Abs_complex(x2,y2) = Abs_complex(x1-x2,y1-y2)"
apply (unfold complex_diff_def)
apply (simp (no_asm) add: complex_add complex_minus)
done

lemma complex_diff_eq_eq: "((x::complex) - y = z) = (x = z + y)"
by (auto simp add: complex_add_minus_left complex_diff_def complex_add_assoc)


subsection{*Multiplication*}

lemma complex_mult:
      "Abs_complex(x1,y1) * Abs_complex(x2,y2) =
       Abs_complex(x1*x2 - y1*y2,x1*y2 + y1*x2)"
apply (unfold complex_mult_def)
apply (simp (no_asm))
done

lemma complex_mult_commute: "(w::complex) * z = z * w"
apply (unfold complex_mult_def)
apply (simp (no_asm) add: real_mult_commute real_add_commute)
done

lemma complex_mult_assoc: "((u::complex) * v) * w = u * (v * w)"
apply (unfold complex_mult_def)
apply (simp (no_asm) add: complex_Re_Im_cancel_iff real_mult_assoc right_diff_distrib right_distrib left_diff_distrib left_distrib mult_left_commute)
done

lemma complex_mult_left_commute: "(x::complex) * (y * z) = y * (x * z)"
apply (unfold complex_mult_def)
apply (simp (no_asm) add: complex_Re_Im_cancel_iff mult_left_commute right_diff_distrib right_distrib)
done

lemmas complex_mult_ac = complex_mult_assoc complex_mult_commute
                      complex_mult_left_commute

lemma complex_mult_one_left: "(1::complex) * z = z"
apply (unfold complex_one_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_mult)
done
declare complex_mult_one_left [simp]

lemma complex_mult_one_right: "z * (1::complex) = z"
apply (simp (no_asm) add: complex_mult_commute)
done
declare complex_mult_one_right [simp]

lemma complex_mult_zero_left: "(0::complex) * z = 0"
apply (unfold complex_zero_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_mult)
done
declare complex_mult_zero_left [simp]

lemma complex_mult_zero_right: "z * 0 = (0::complex)"
apply (simp (no_asm) add: complex_mult_commute)
done
declare complex_mult_zero_right [simp]

lemma complex_divide_zero: "0 / z = (0::complex)"
by (unfold complex_divide_def, auto)
declare complex_divide_zero [simp]

lemma complex_minus_mult_eq1: "-(x * y) = -x * (y::complex)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_mult complex_minus real_diff_def)
done

lemma complex_minus_mult_eq2: "-(x * y) = x * -(y::complex)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_mult complex_minus real_diff_def)
done

lemma complex_add_mult_distrib: "((z1::complex) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule_tac z = z1 in eq_Abs_complex)
apply (rule_tac z = z2 in eq_Abs_complex)
apply (rule_tac z = w in eq_Abs_complex)
apply (auto simp add: complex_mult complex_add left_distrib real_diff_def add_ac)
done

lemma complex_add_mult_distrib2: "(w::complex) * (z1 + z2) = (w * z1) + (w * z2)"
apply (rule_tac z1 = "z1 + z2" in complex_mult_commute [THEN ssubst])
apply (simp (no_asm) add: complex_add_mult_distrib)
apply (simp (no_asm) add: complex_mult_commute)
done

lemma complex_zero_not_eq_one: "(0::complex) \<noteq> 1"
apply (unfold complex_zero_def complex_one_def)
apply (simp (no_asm) add: complex_Re_Im_cancel_iff)
done
declare complex_zero_not_eq_one [simp]
declare complex_zero_not_eq_one [THEN not_sym, simp]


subsection{*Inverse*}

lemma complex_inverse:
     "inverse (Abs_complex(x,y)) =
      Abs_complex(x/(x ^ 2 + y ^ 2),-y/(x ^ 2 + y ^ 2))"
apply (unfold complex_inverse_def)
apply (simp (no_asm))
done

lemma COMPLEX_INVERSE_ZERO: "inverse 0 = (0::complex)"
by (unfold complex_inverse_def complex_zero_def, auto)

lemma COMPLEX_DIVISION_BY_ZERO: "a / (0::complex) = 0"
apply (simp (no_asm) add: complex_divide_def COMPLEX_INVERSE_ZERO)
done

instance complex :: division_by_zero
proof
  fix x :: complex
  show "inverse 0 = (0::complex)" by (rule COMPLEX_INVERSE_ZERO)
  show "x/0 = 0" by (rule COMPLEX_DIVISION_BY_ZERO) 
qed

lemma complex_mult_inv_left: "z \<noteq> (0::complex) ==> inverse(z) * z = 1"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_mult complex_inverse complex_one_def 
       complex_zero_def add_divide_distrib [symmetric] power2_eq_square mult_ac)
apply (drule_tac y = y in real_sum_squares_not_zero)
apply (drule_tac [2] x = x in real_sum_squares_not_zero2, auto)
done
declare complex_mult_inv_left [simp]

lemma complex_mult_inv_right: "z \<noteq> (0::complex) ==> z * inverse(z) = 1"
by (auto intro: complex_mult_commute [THEN subst])
declare complex_mult_inv_right [simp]


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
    by (rule complex_zero_not_eq_one) 
  show "(u + v) * w = u * w + v * w"
    by (rule complex_add_mult_distrib) 
  show "z+u = z+v ==> u=v"
    proof -
      assume eq: "z+u = z+v" 
      hence "(-z + z) + u = (-z + z) + v" by (simp only: eq complex_add_assoc)
      thus "u = v" by (simp add: complex_add_minus_left)
    qed
  assume neq: "w \<noteq> 0"
  thus "z / w = z * inverse w"
    by (simp add: complex_divide_def)
  show "inverse w * w = 1"
    by (simp add: neq complex_mult_inv_left) 
qed


lemma complex_minus_mult_commute: "-x * y = x * -(y::complex)"
apply (simp)
done

subsection{*Embedding Properties for @{term complex_of_real} Map*}

lemma inj_complex_of_real: "inj complex_of_real"
apply (rule inj_onI)
apply (auto dest: inj_Abs_complex [THEN injD] simp add: complex_of_real_def)
done

lemma complex_of_real_one:
      "complex_of_real 1 = 1"
apply (unfold complex_one_def complex_of_real_def)
apply (rule refl)
done
declare complex_of_real_one [simp]

lemma complex_of_real_zero:
      "complex_of_real 0 = 0"
apply (unfold complex_zero_def complex_of_real_def)
apply (rule refl)
done
declare complex_of_real_zero [simp]

lemma complex_of_real_eq_iff:
     "(complex_of_real x = complex_of_real y) = (x = y)"
by (auto dest: inj_complex_of_real [THEN injD])
declare complex_of_real_eq_iff [iff]

lemma complex_of_real_minus: "complex_of_real(-x) = - complex_of_real x"
apply (simp (no_asm) add: complex_of_real_def complex_minus)
done

lemma complex_of_real_inverse:
 "complex_of_real(inverse x) = inverse(complex_of_real x)"
apply (case_tac "x=0", simp)
apply (simp add: complex_inverse complex_of_real_def real_divide_def 
                 inverse_mult_distrib power2_eq_square)
done

lemma complex_of_real_add:
 "complex_of_real x + complex_of_real y = complex_of_real (x + y)"
apply (simp (no_asm) add: complex_add complex_of_real_def)
done

lemma complex_of_real_diff:
 "complex_of_real x - complex_of_real y = complex_of_real (x - y)"
apply (simp (no_asm) add: complex_of_real_minus [symmetric] complex_diff_def complex_of_real_add)
done

lemma complex_of_real_mult:
 "complex_of_real x * complex_of_real y = complex_of_real (x * y)"
apply (simp (no_asm) add: complex_mult complex_of_real_def)
done

lemma complex_of_real_divide:
      "complex_of_real x / complex_of_real y = complex_of_real(x/y)"
apply (unfold complex_divide_def)
apply (case_tac "y=0")
apply (simp (no_asm_simp) add: DIVISION_BY_ZERO COMPLEX_INVERSE_ZERO)
apply (simp (no_asm_simp) add: complex_of_real_mult [symmetric] complex_of_real_inverse real_divide_def)
done

lemma complex_mod: "cmod (Abs_complex(x,y)) = sqrt(x ^ 2 + y ^ 2)"
apply (unfold cmod_def)
apply (simp (no_asm))
done

lemma complex_mod_zero: "cmod(0) = 0"
apply (unfold cmod_def)
apply (simp (no_asm))
done
declare complex_mod_zero [simp]

lemma complex_mod_one [simp]: "cmod(1) = 1"
by (simp add: cmod_def power2_eq_square)

lemma complex_mod_complex_of_real: "cmod(complex_of_real x) = abs x"
apply (simp add: complex_of_real_def power2_eq_square complex_mod)
done
declare complex_mod_complex_of_real [simp]

lemma complex_of_real_abs:
     "complex_of_real (abs x) = complex_of_real(cmod(complex_of_real x))"
by (simp)



subsection{*Conjugation is an Automorphism*}

lemma complex_cnj: "cnj (Abs_complex(x,y)) = Abs_complex(x,-y)"
apply (unfold cnj_def)
apply (simp (no_asm))
done

lemma inj_cnj: "inj cnj"
apply (rule inj_onI)
apply (auto simp add: cnj_def Abs_complex_cancel_iff complex_Re_Im_cancel_iff)
done

lemma complex_cnj_cancel_iff: "(cnj x = cnj y) = (x = y)"
by (auto dest: inj_cnj [THEN injD])
declare complex_cnj_cancel_iff [simp]

lemma complex_cnj_cnj: "cnj (cnj z) = z"
apply (unfold cnj_def)
apply (simp (no_asm))
done
declare complex_cnj_cnj [simp]

lemma complex_cnj_complex_of_real:
 "cnj (complex_of_real x) = complex_of_real x"
apply (unfold complex_of_real_def)
apply (simp (no_asm) add: complex_cnj)
done
declare complex_cnj_complex_of_real [simp]

lemma complex_mod_cnj: "cmod (cnj z) = cmod z"
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_cnj complex_mod power2_eq_square)
done
declare complex_mod_cnj [simp]

lemma complex_cnj_minus: "cnj (-z) = - cnj z"
apply (unfold cnj_def)
apply (simp (no_asm) add: complex_minus complex_Re_minus complex_Im_minus)
done

lemma complex_cnj_inverse: "cnj(inverse z) = inverse(cnj z)"
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_cnj complex_inverse power2_eq_square)
done

lemma complex_cnj_add: "cnj(w + z) = cnj(w) + cnj(z)"
apply (rule_tac z = w in eq_Abs_complex)
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_cnj complex_add)
done

lemma complex_cnj_diff: "cnj(w - z) = cnj(w) - cnj(z)"
apply (unfold complex_diff_def)
apply (simp (no_asm) add: complex_cnj_add complex_cnj_minus)
done

lemma complex_cnj_mult: "cnj(w * z) = cnj(w) * cnj(z)"
apply (rule_tac z = w in eq_Abs_complex)
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_cnj complex_mult)
done

lemma complex_cnj_divide: "cnj(w / z) = (cnj w)/(cnj z)"
apply (unfold complex_divide_def)
apply (simp (no_asm) add: complex_cnj_mult complex_cnj_inverse)
done

lemma complex_cnj_one: "cnj 1 = 1"
apply (unfold cnj_def complex_one_def)
apply (simp (no_asm))
done
declare complex_cnj_one [simp]

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re(z))"
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_add complex_cnj complex_of_real_def)
done

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im(z)) * ii"
apply (rule_tac z = z in eq_Abs_complex)
apply (simp add: complex_add complex_cnj complex_of_real_def complex_diff_def 
                 complex_minus i_def complex_mult)
done

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
by (simp add: cnj_def complex_zero_def)

lemma complex_cnj_zero_iff: "(cnj z = 0) = (z = 0)"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_zero_def complex_cnj)
done
declare complex_cnj_zero_iff [iff]

lemma complex_mult_cnj: "z * cnj z = complex_of_real (Re(z) ^ 2 + Im(z) ^ 2)"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_cnj complex_mult complex_of_real_def power2_eq_square)
done


subsection{*Algebra*}

lemma complex_add_left_cancel_zero: "(x + y = x) = (y = (0::complex))"
apply (unfold complex_zero_def)
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_add)
done
declare complex_add_left_cancel_zero [simp]

lemma complex_diff_mult_distrib:
      "((z1::complex) - z2) * w = (z1 * w) - (z2 * w)"
apply (unfold complex_diff_def)
apply (simp (no_asm) add: complex_add_mult_distrib)
done

lemma complex_diff_mult_distrib2:
      "(w::complex) * (z1 - z2) = (w * z1) - (w * z2)"
apply (unfold complex_diff_def)
apply (simp (no_asm) add: complex_add_mult_distrib2)
done


subsection{*Modulus*}

lemma complex_mod_eq_zero_cancel: "(cmod x = 0) = (x = 0)"
apply (rule_tac z = x in eq_Abs_complex)
apply (auto intro: real_sum_squares_cancel real_sum_squares_cancel2 simp add: complex_mod complex_zero_def power2_eq_square)
done
declare complex_mod_eq_zero_cancel [simp]

lemma complex_mod_complex_of_real_of_nat: "cmod (complex_of_real(real (n::nat))) = real n"
apply (simp (no_asm))
done
declare complex_mod_complex_of_real_of_nat [simp]

lemma complex_mod_minus: "cmod (-x) = cmod(x)"
apply (rule_tac z = x in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_mod complex_minus power2_eq_square)
done
declare complex_mod_minus [simp]

lemma complex_mod_mult_cnj: "cmod(z * cnj(z)) = cmod(z) ^ 2"
apply (rule_tac z = z in eq_Abs_complex)
apply (simp (no_asm_simp) add: complex_mod complex_cnj complex_mult);
apply (simp (no_asm) add: power2_eq_square real_abs_def)
done

lemma complex_mod_squared: "cmod(Abs_complex(x,y)) ^ 2 = x ^ 2 + y ^ 2"
by (unfold cmod_def, auto)

lemma complex_mod_ge_zero: "0 \<le> cmod x"
apply (unfold cmod_def)
apply (auto intro: real_sqrt_ge_zero)
done
declare complex_mod_ge_zero [simp]

lemma abs_cmod_cancel: "abs(cmod x) = cmod x"
by (auto intro: abs_eqI1)
declare abs_cmod_cancel [simp]

lemma complex_mod_mult: "cmod(x*y) = cmod(x) * cmod(y)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_mult complex_mod real_sqrt_mult_distrib2 [symmetric] simp del: realpow_Suc)
apply (rule_tac n = 1 in power_inject_base)
apply (auto simp add: power2_eq_square [symmetric] simp del: realpow_Suc)
apply (auto simp add: real_diff_def power2_eq_square right_distrib left_distrib add_ac mult_ac)
done

lemma complex_mod_add_squared_eq: "cmod(x + y) ^ 2 = cmod(x) ^ 2 + cmod(y) ^ 2 + 2 * Re(x * cnj y)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_add complex_mod_squared complex_mult complex_cnj real_diff_def simp del: realpow_Suc)
apply (auto simp add: right_distrib left_distrib power2_eq_square mult_ac add_ac)
done

lemma complex_Re_mult_cnj_le_cmod: "Re(x * cnj y) \<le> cmod(x * cnj y)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_mod complex_mult complex_cnj real_diff_def simp del: realpow_Suc)
done
declare complex_Re_mult_cnj_le_cmod [simp]

lemma complex_Re_mult_cnj_le_cmod2: "Re(x * cnj y) \<le> cmod(x * y)"
apply (cut_tac x = x and y = y in complex_Re_mult_cnj_le_cmod)
apply (simp add: complex_mod_mult)
done
declare complex_Re_mult_cnj_le_cmod2 [simp]

lemma real_sum_squared_expand: "((x::real) + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y"
apply (simp (no_asm) add: left_distrib right_distrib power2_eq_square)
done

lemma complex_mod_triangle_squared: "cmod (x + y) ^ 2 \<le> (cmod(x) + cmod(y)) ^ 2"
apply (simp (no_asm) add: real_sum_squared_expand complex_mod_add_squared_eq real_mult_assoc complex_mod_mult [symmetric])
done
declare complex_mod_triangle_squared [simp]

lemma complex_mod_minus_le_complex_mod: "- cmod x \<le> cmod x"
apply (rule order_trans [OF _ complex_mod_ge_zero]) 
apply (simp (no_asm))
done
declare complex_mod_minus_le_complex_mod [simp]

lemma complex_mod_triangle_ineq: "cmod (x + y) \<le> cmod(x) + cmod(y)"
apply (rule_tac n = 1 in realpow_increasing)
apply (auto intro:  order_trans [OF _ complex_mod_ge_zero]
            simp add: power2_eq_square [symmetric])
done
declare complex_mod_triangle_ineq [simp]

lemma complex_mod_triangle_ineq2: "cmod(b + a) - cmod b \<le> cmod a"
apply (cut_tac x1 = b and y1 = a and c = "-cmod b" 
       in complex_mod_triangle_ineq [THEN add_right_mono])
apply (simp (no_asm))
done
declare complex_mod_triangle_ineq2 [simp]

lemma complex_mod_diff_commute: "cmod (x - y) = cmod (y - x)"
apply (rule_tac z = x in eq_Abs_complex)
apply (rule_tac z = y in eq_Abs_complex)
apply (auto simp add: complex_diff complex_mod right_diff_distrib power2_eq_square left_diff_distrib add_ac mult_ac)
done

lemma complex_mod_add_less: "[| cmod x < r; cmod y < s |] ==> cmod (x + y) < r + s"
by (auto intro: order_le_less_trans complex_mod_triangle_ineq)

lemma complex_mod_mult_less: "[| cmod x < r; cmod y < s |] ==> cmod (x * y) < r * s"
by (auto intro: real_mult_less_mono' simp add: complex_mod_mult)

lemma complex_mod_diff_ineq: "cmod(a) - cmod(b) \<le> cmod(a + b)"
apply (rule linorder_cases [of "cmod(a)" "cmod (b)"])
apply auto
apply (rule order_trans [of _ 0], rule order_less_imp_le)
apply (simp add: compare_rls, simp)  
apply (simp add: compare_rls)
apply (rule complex_mod_minus [THEN subst])
apply (rule order_trans)
apply (rule_tac [2] complex_mod_triangle_ineq)
apply (auto simp add: complex_add_ac)
done
declare complex_mod_diff_ineq [simp]

lemma complex_Re_le_cmod: "Re z \<le> cmod z"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_mod simp del: realpow_Suc)
done
declare complex_Re_le_cmod [simp]

lemma complex_mod_gt_zero: "z \<noteq> 0 ==> 0 < cmod z"
apply (cut_tac x = z in complex_mod_ge_zero)
apply (drule order_le_imp_less_or_eq, auto)
done


subsection{*A Few More Theorems*}

lemma complex_mod_inverse: "cmod(inverse x) = inverse(cmod x)"
apply (case_tac "x=0", simp add: COMPLEX_INVERSE_ZERO)
apply (rule_tac c1 = "cmod x" in real_mult_left_cancel [THEN iffD1])
apply (auto simp add: complex_mod_mult [symmetric])
done

lemma complex_mod_divide:
      "cmod(x/y) = cmod(x)/(cmod y)"
apply (unfold complex_divide_def real_divide_def)
apply (auto simp add: complex_mod_mult complex_mod_inverse)
done

lemma complex_inverse_divide:
      "inverse(x/y) = y/(x::complex)"
apply (unfold complex_divide_def)
apply (auto simp add: inverse_mult_distrib complex_mult_commute)
done
declare complex_inverse_divide [simp]


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

lemma complexpow_minus: "(-x::complex) ^ n = (if even n then (x ^ n) else -(x ^ n))"
by (induct_tac "n", auto)

lemma complexpow_i_squared [simp]: "ii ^ 2 = -(1::complex)"
by (simp add: i_def complex_mult complex_one_def complex_minus numeral_2_eq_2)

lemma complex_i_not_zero [simp]: "ii \<noteq> 0"
by (unfold i_def complex_zero_def, auto)


subsection{*The Function @{term sgn}*}

lemma sgn_zero: "sgn 0 = 0"
apply (unfold sgn_def)
apply (simp (no_asm))
done
declare sgn_zero [simp]

lemma sgn_one: "sgn 1 = 1"
apply (unfold sgn_def)
apply (simp (no_asm))
done
declare sgn_one [simp]

lemma sgn_minus: "sgn (-z) = - sgn(z)"
by (unfold sgn_def, auto)

lemma sgn_eq:
    "sgn z = z / complex_of_real (cmod z)"
apply (unfold sgn_def)
apply (simp (no_asm))
done

lemma complex_split: "\<exists>x y. z = complex_of_real(x) + ii * complex_of_real(y)"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_of_real_def i_def complex_mult complex_add)
done

lemma Re_complex_i: "Re(complex_of_real(x) + ii * complex_of_real(y)) = x"
by (auto simp add: complex_of_real_def i_def complex_mult complex_add)
declare Re_complex_i [simp]

lemma Im_complex_i: "Im(complex_of_real(x) + ii * complex_of_real(y)) = y"
by (auto simp add: complex_of_real_def i_def complex_mult complex_add)
declare Im_complex_i [simp]

lemma i_mult_eq: "ii * ii = complex_of_real (-1)"
apply (unfold i_def complex_of_real_def)
apply (auto simp add: complex_mult complex_add)
done

lemma i_mult_eq2: "ii * ii = -(1::complex)"
apply (unfold i_def complex_one_def)
apply (simp (no_asm) add: complex_mult complex_minus)
done
declare i_mult_eq2 [simp]

lemma cmod_i: "cmod (complex_of_real(x) + ii * complex_of_real(y)) =
      sqrt (x ^ 2 + y ^ 2)"
apply (auto simp add: complex_mult complex_add i_def complex_of_real_def cmod_def)
done

lemma complex_eq_Re_eq:
     "complex_of_real xa + ii * complex_of_real ya =
      complex_of_real xb + ii * complex_of_real yb
       ==> xa = xb"
apply (unfold complex_of_real_def i_def)
apply (auto simp add: complex_mult complex_add)
done

lemma complex_eq_Im_eq:
     "complex_of_real xa + ii * complex_of_real ya =
      complex_of_real xb + ii * complex_of_real yb
       ==> ya = yb"
apply (unfold complex_of_real_def i_def)
apply (auto simp add: complex_mult complex_add)
done

lemma complex_eq_cancel_iff: "(complex_of_real xa + ii * complex_of_real ya =
       complex_of_real xb + ii * complex_of_real yb) = ((xa = xb) & (ya = yb))"
apply (auto intro: complex_eq_Im_eq complex_eq_Re_eq)
done
declare complex_eq_cancel_iff [iff]

lemma complex_eq_cancel_iffA: "(complex_of_real xa + complex_of_real ya * ii =
       complex_of_real xb + complex_of_real yb * ii ) = ((xa = xb) & (ya = yb))"
apply (auto simp add: complex_mult_commute)
done
declare complex_eq_cancel_iffA [iff]

lemma complex_eq_cancel_iffB: "(complex_of_real xa + complex_of_real ya * ii =
       complex_of_real xb + ii * complex_of_real yb) = ((xa = xb) & (ya = yb))"
apply (auto simp add: complex_mult_commute)
done
declare complex_eq_cancel_iffB [iff]

lemma complex_eq_cancel_iffC: "(complex_of_real xa + ii * complex_of_real ya  =
       complex_of_real xb + complex_of_real yb * ii) = ((xa = xb) & (ya = yb))"
apply (auto simp add: complex_mult_commute)
done
declare complex_eq_cancel_iffC [iff]

lemma complex_eq_cancel_iff2: "(complex_of_real x + ii * complex_of_real y =
      complex_of_real xa) = (x = xa & y = 0)"
apply (cut_tac xa = x and ya = y and xb = xa and yb = 0 in complex_eq_cancel_iff)
apply (simp del: complex_eq_cancel_iff)
done
declare complex_eq_cancel_iff2 [simp]

lemma complex_eq_cancel_iff2a: "(complex_of_real x + complex_of_real y * ii =
      complex_of_real xa) = (x = xa & y = 0)"
apply (auto simp add: complex_mult_commute)
done
declare complex_eq_cancel_iff2a [simp]

lemma complex_eq_cancel_iff3: "(complex_of_real x + ii * complex_of_real y =
      ii * complex_of_real ya) = (x = 0 & y = ya)"
apply (cut_tac xa = x and ya = y and xb = 0 and yb = ya in complex_eq_cancel_iff)
apply (simp del: complex_eq_cancel_iff)
done
declare complex_eq_cancel_iff3 [simp]

lemma complex_eq_cancel_iff3a: "(complex_of_real x + complex_of_real y * ii =
      ii * complex_of_real ya) = (x = 0 & y = ya)"
apply (auto simp add: complex_mult_commute)
done
declare complex_eq_cancel_iff3a [simp]

lemma complex_split_Re_zero:
     "complex_of_real x + ii * complex_of_real y = 0
      ==> x = 0"
apply (unfold complex_of_real_def i_def complex_zero_def)
apply (auto simp add: complex_mult complex_add)
done

lemma complex_split_Im_zero:
     "complex_of_real x + ii * complex_of_real y = 0
      ==> y = 0"
apply (unfold complex_of_real_def i_def complex_zero_def)
apply (auto simp add: complex_mult complex_add)
done

lemma Re_sgn:
      "Re(sgn z) = Re(z)/cmod z"
apply (unfold sgn_def complex_divide_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_of_real_inverse [symmetric])
apply (auto simp add: complex_of_real_def complex_mult real_divide_def)
done
declare Re_sgn [simp]

lemma Im_sgn:
      "Im(sgn z) = Im(z)/cmod z"
apply (unfold sgn_def complex_divide_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_of_real_inverse [symmetric])
apply (auto simp add: complex_of_real_def complex_mult real_divide_def)
done
declare Im_sgn [simp]

lemma complex_inverse_complex_split:
     "inverse(complex_of_real x + ii * complex_of_real y) =
      complex_of_real(x/(x ^ 2 + y ^ 2)) -
      ii * complex_of_real(y/(x ^ 2 + y ^ 2))"
apply (unfold complex_of_real_def i_def)
apply (auto simp add: complex_mult complex_add complex_diff_def complex_minus complex_inverse real_divide_def)
done

(*----------------------------------------------------------------------------*)
(* Many of the theorems below need to be moved elsewhere e.g. Transc. Also *)
(* many of the theorems are not used - so should they be kept?                *)
(*----------------------------------------------------------------------------*)

lemma complex_of_real_zero_iff [simp]: "(complex_of_real y = 0) = (y = 0)"
by (auto simp add: complex_zero_def complex_of_real_def)

lemma Re_mult_i_eq:
    "Re (ii * complex_of_real y) = 0"
apply (unfold i_def complex_of_real_def)
apply (auto simp add: complex_mult)
done
declare Re_mult_i_eq [simp]

lemma Im_mult_i_eq:
    "Im (ii * complex_of_real y) = y"
apply (unfold i_def complex_of_real_def)
apply (auto simp add: complex_mult)
done
declare Im_mult_i_eq [simp]

lemma complex_mod_mult_i:
    "cmod (ii * complex_of_real y) = abs y"
apply (unfold i_def complex_of_real_def)
apply (auto simp add: complex_mult complex_mod power2_eq_square)
done
declare complex_mod_mult_i [simp]

lemma cos_arg_i_mult_zero_pos:
   "0 < y ==> cos (arg(ii * complex_of_real y)) = 0"
apply (unfold arg_def)
apply (auto simp add: abs_eqI2)
apply (rule_tac a = "pi/2" in someI2, auto)
apply (rule order_less_trans [of _ 0], auto)
done

lemma cos_arg_i_mult_zero_neg:
   "y < 0 ==> cos (arg(ii * complex_of_real y)) = 0"
apply (unfold arg_def)
apply (auto simp add: abs_minus_eqI2)
apply (rule_tac a = "- pi/2" in someI2, auto)
apply (rule order_trans [of _ 0], auto)
done

lemma cos_arg_i_mult_zero [simp]
    : "y \<noteq> 0 ==> cos (arg(ii * complex_of_real y)) = 0"
by (cut_tac x = y and y = 0 in linorder_less_linear, 
    auto simp add: cos_arg_i_mult_zero_pos cos_arg_i_mult_zero_neg)


subsection{*Finally! Polar Form for Complex Numbers*}

lemma complex_split_polar: "\<exists>r a. z = complex_of_real r *
      (complex_of_real(cos a) + ii * complex_of_real(sin a))"
apply (cut_tac z = z in complex_split)
apply (auto simp add: polar_Ex right_distrib complex_of_real_mult mult_ac)
done

lemma rcis_Ex: "\<exists>r a. z = rcis r a"
apply (unfold rcis_def cis_def)
apply (rule complex_split_polar)
done

lemma Re_complex_polar: "Re(complex_of_real r *
      (complex_of_real(cos a) + ii * complex_of_real(sin a))) = r * cos a"
apply (auto simp add: complex_add_mult_distrib2 complex_of_real_mult complex_mult_ac)
done
declare Re_complex_polar [simp]

lemma Re_rcis: "Re(rcis r a) = r * cos a"
by (unfold rcis_def cis_def, auto)
declare Re_rcis [simp]

lemma Im_complex_polar [simp]:
     "Im(complex_of_real r * 
         (complex_of_real(cos a) + ii * complex_of_real(sin a))) = 
      r * sin a"
by (auto simp add: complex_add_mult_distrib2 complex_of_real_mult mult_ac)

lemma Im_rcis [simp]: "Im(rcis r a) = r * sin a"
by (unfold rcis_def cis_def, auto)

lemma complex_mod_complex_polar [simp]:
     "cmod (complex_of_real r * 
            (complex_of_real(cos a) + ii * complex_of_real(sin a))) = 
      abs r"
by (auto simp add: complex_add_mult_distrib2 cmod_i complex_of_real_mult
                      right_distrib [symmetric] power_mult_distrib mult_ac 
         simp del: realpow_Suc)

lemma complex_mod_rcis: "cmod(rcis r a) = abs r"
by (unfold rcis_def cis_def, auto)
declare complex_mod_rcis [simp]

lemma complex_mod_sqrt_Re_mult_cnj: "cmod z = sqrt (Re (z * cnj z))"
apply (unfold cmod_def)
apply (rule real_sqrt_eq_iff [THEN iffD2])
apply (auto simp add: complex_mult_cnj)
done

lemma complex_Re_cnj: "Re(cnj z) = Re z"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_cnj)
done
declare complex_Re_cnj [simp]

lemma complex_Im_cnj: "Im(cnj z) = - Im z"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_cnj)
done
declare complex_Im_cnj [simp]

lemma complex_In_mult_cnj_zero: "Im (z * cnj z) = 0"
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_cnj complex_mult)
done
declare complex_In_mult_cnj_zero [simp]

lemma complex_Re_mult: "[| Im w = 0; Im z = 0 |] ==> Re(w * z) = Re(w) * Re(z)"
apply (rule_tac z = z in eq_Abs_complex)
apply (rule_tac z = w in eq_Abs_complex)
apply (auto simp add: complex_mult)
done

lemma complex_Re_mult_complex_of_real: "Re (z * complex_of_real c) = Re(z) * c"
apply (unfold complex_of_real_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_mult)
done
declare complex_Re_mult_complex_of_real [simp]

lemma complex_Im_mult_complex_of_real: "Im (z * complex_of_real c) = Im(z) * c"
apply (unfold complex_of_real_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_mult)
done
declare complex_Im_mult_complex_of_real [simp]

lemma complex_Re_mult_complex_of_real2: "Re (complex_of_real c * z) = c * Re(z)"
apply (unfold complex_of_real_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_mult)
done
declare complex_Re_mult_complex_of_real2 [simp]

lemma complex_Im_mult_complex_of_real2: "Im (complex_of_real c * z) = c * Im(z)"
apply (unfold complex_of_real_def)
apply (rule_tac z = z in eq_Abs_complex)
apply (auto simp add: complex_mult)
done
declare complex_Im_mult_complex_of_real2 [simp]

(*---------------------------------------------------------------------------*)
(*  (r1 * cis a) * (r2 * cis b) = r1 * r2 * cis (a + b)                      *)
(*---------------------------------------------------------------------------*)

lemma cis_rcis_eq: "cis a = rcis 1 a"
apply (unfold rcis_def)
apply (simp (no_asm))
done

lemma rcis_mult:
  "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)"
apply (unfold rcis_def cis_def)
apply (auto simp add: cos_add sin_add complex_add_mult_distrib2 complex_add_mult_distrib complex_mult_ac complex_add_ac)
apply (auto simp add: complex_add_mult_distrib2 [symmetric] complex_mult_assoc [symmetric] complex_of_real_mult complex_of_real_add complex_add_assoc [symmetric] i_mult_eq simp del: i_mult_eq2)
apply (auto simp add: complex_add_ac)
apply (auto simp add: complex_add_assoc [symmetric] complex_of_real_add right_distrib real_diff_def mult_ac add_ac)
done

lemma cis_mult: "cis a * cis b = cis (a + b)"
apply (simp (no_asm) add: cis_rcis_eq rcis_mult)
done

lemma cis_zero: "cis 0 = 1"
by (unfold cis_def, auto)
declare cis_zero [simp]

lemma cis_zero2: "cis 0 = complex_of_real 1"
by (unfold cis_def, auto)
declare cis_zero2 [simp]

lemma rcis_zero_mod: "rcis 0 a = 0"
apply (unfold rcis_def)
apply (simp (no_asm))
done
declare rcis_zero_mod [simp]

lemma rcis_zero_arg: "rcis r 0 = complex_of_real r"
apply (unfold rcis_def)
apply (simp (no_asm))
done
declare rcis_zero_arg [simp]

lemma complex_of_real_minus_one:
   "complex_of_real (-(1::real)) = -(1::complex)"
apply (unfold complex_of_real_def complex_one_def)
apply (simp (no_asm) add: complex_minus)
done

lemma complex_i_mult_minus: "ii * (ii * x) = - x"
apply (simp (no_asm) add: complex_mult_assoc [symmetric])
done
declare complex_i_mult_minus [simp]

lemma complex_i_mult_minus2: "ii * ii * x = - x"
apply (simp (no_asm))
done
declare complex_i_mult_minus2 [simp]

lemma cis_real_of_nat_Suc_mult:
   "cis (real (Suc n) * a) = cis a * cis (real n * a)"
apply (unfold cis_def)
apply (auto simp add: real_of_nat_Suc left_distrib cos_add sin_add complex_add_mult_distrib complex_add_mult_distrib2 complex_of_real_add complex_of_real_mult complex_mult_ac complex_add_ac)
apply (auto simp add: complex_add_mult_distrib2 [symmetric] complex_mult_assoc [symmetric] i_mult_eq complex_of_real_mult complex_of_real_add complex_add_assoc [symmetric] complex_of_real_minus [symmetric] real_diff_def mult_ac simp del: i_mult_eq2)
done

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
apply (induct_tac "n")
apply (auto simp add: cis_real_of_nat_Suc_mult)
done

lemma DeMoivre2:
   "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
apply (unfold rcis_def)
apply (auto simp add: power_mult_distrib DeMoivre complex_of_real_pow)
done

lemma cis_inverse: "inverse(cis a) = cis (-a)"
apply (unfold cis_def)
apply (auto simp add: complex_inverse_complex_split complex_of_real_minus complex_diff_def)
done
declare cis_inverse [simp]

lemma rcis_inverse: "inverse(rcis r a) = rcis (1/r) (-a)"
apply (case_tac "r=0", simp)
apply (auto simp add: complex_inverse_complex_split right_distrib 
            complex_of_real_mult rcis_def cis_def power2_eq_square mult_ac)
apply (auto simp add: right_distrib [symmetric] complex_of_real_minus complex_diff_def)
done

lemma cis_divide: "cis a / cis b = cis (a - b)"
apply (unfold complex_divide_def)
apply (auto simp add: cis_mult real_diff_def)
done

lemma rcis_divide: "rcis r1 a / rcis r2 b = rcis (r1/r2) (a - b)"
apply (unfold complex_divide_def)
apply (case_tac "r2=0")
apply (simp (no_asm_simp) add: DIVISION_BY_ZERO COMPLEX_INVERSE_ZERO)
apply (auto simp add: rcis_inverse rcis_mult real_diff_def)
done

lemma Re_cis: "Re(cis a) = cos a"
by (unfold cis_def, auto)
declare Re_cis [simp]

lemma Im_cis: "Im(cis a) = sin a"
by (unfold cis_def, auto)
declare Im_cis [simp]

lemma cos_n_Re_cis_pow_n: "cos (real n * a) = Re(cis a ^ n)"
by (auto simp add: DeMoivre)

lemma sin_n_Im_cis_pow_n: "sin (real n * a) = Im(cis a ^ n)"
by (auto simp add: DeMoivre)

lemma expi_Im_split:
    "expi (ii * complex_of_real y) =
     complex_of_real (cos y) + ii * complex_of_real (sin y)"
by (unfold expi_def cis_def, auto)

lemma expi_Im_cis:
    "expi (ii * complex_of_real y) = cis y"
by (unfold expi_def, auto)

lemma expi_add: "expi(a + b) = expi(a) * expi(b)"
apply (unfold expi_def)
apply (auto simp add: complex_Re_add exp_add complex_Im_add cis_mult [symmetric] complex_of_real_mult complex_mult_ac)
done

lemma expi_complex_split:
     "expi(complex_of_real x + ii * complex_of_real y) =
      complex_of_real (exp(x)) * cis y"
by (unfold expi_def, auto)

lemma expi_zero: "expi (0::complex) = 1"
by (unfold expi_def, auto)
declare expi_zero [simp]

lemma complex_Re_mult_eq: "Re (w * z) = Re w * Re z - Im w * Im z"
apply (rule_tac z = z in eq_Abs_complex)
apply (rule_tac z = w in eq_Abs_complex)
apply (auto simp add: complex_mult)
done

lemma complex_Im_mult_eq:
     "Im (w * z) = Re w * Im z + Im w * Re z"
apply (rule_tac z = z in eq_Abs_complex)
apply (rule_tac z = w in eq_Abs_complex)
apply (auto simp add: complex_mult)
done

lemma complex_expi_Ex: 
   "\<exists>a r. z = complex_of_real r * expi a"
apply (cut_tac z = z in rcis_Ex)
apply (auto simp add: expi_def rcis_def complex_mult_assoc [symmetric] complex_of_real_mult)
apply (rule_tac x = "ii * complex_of_real a" in exI, auto)
done


(****
Goal "[| - pi < a; a \<le> pi |] ==> (-pi < a & a \<le> 0) | (0 \<le> a & a \<le> pi)"
by Auto_tac
qed "lemma_split_interval";

Goalw [arg_def]
  "[| r \<noteq> 0; - pi < a; a \<le> pi |] \
\  ==> arg(complex_of_real r * \
\      (complex_of_real(cos a) + ii * complex_of_real(sin a))) = a";
by Auto_tac
by (cut_inst_tac [("x","0"),("y","r")] linorder_less_linear 1);
by (auto_tac (claset(),simpset() addsimps (map (full_rename_numerals thy)
    [rabs_eqI2,rabs_minus_eqI2,real_minus_rinv]) [real_divide_def,
    minus_mult_right RS sym] mult_ac));
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym]));
by (dtac lemma_split_interval 1 THEN safe)
****)


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

val inj_Rep_complex = thm"inj_Rep_complex";
val inj_Abs_complex = thm"inj_Abs_complex";
val Abs_complex_cancel_iff = thm"Abs_complex_cancel_iff";
val pair_mem_complex = thm"pair_mem_complex";
val Abs_complex_inverse2 = thm"Abs_complex_inverse2";
val eq_Abs_complex = thm"eq_Abs_complex";
val Re = thm"Re";
val Im = thm"Im";
val Abs_complex_cancel = thm"Abs_complex_cancel";
val complex_Re_Im_cancel_iff = thm"complex_Re_Im_cancel_iff";
val complex_Re_zero = thm"complex_Re_zero";
val complex_Im_zero = thm"complex_Im_zero";
val complex_Re_one = thm"complex_Re_one";
val complex_Im_one = thm"complex_Im_one";
val complex_Re_i = thm"complex_Re_i";
val complex_Im_i = thm"complex_Im_i";
val Re_complex_of_real_zero = thm"Re_complex_of_real_zero";
val Im_complex_of_real_zero = thm"Im_complex_of_real_zero";
val Re_complex_of_real_one = thm"Re_complex_of_real_one";
val Im_complex_of_real_one = thm"Im_complex_of_real_one";
val Re_complex_of_real = thm"Re_complex_of_real";
val Im_complex_of_real = thm"Im_complex_of_real";
val complex_minus = thm"complex_minus";
val complex_Re_minus = thm"complex_Re_minus";
val complex_Im_minus = thm"complex_Im_minus";
val complex_minus_minus = thm"complex_minus_minus";
val inj_complex_minus = thm"inj_complex_minus";
val complex_minus_zero = thm"complex_minus_zero";
val complex_minus_zero_iff = thm"complex_minus_zero_iff";
val complex_minus_zero_iff2 = thm"complex_minus_zero_iff2";
val complex_minus_not_zero_iff = thm"complex_minus_not_zero_iff";
val complex_add = thm"complex_add";
val complex_Re_add = thm"complex_Re_add";
val complex_Im_add = thm"complex_Im_add";
val complex_add_commute = thm"complex_add_commute";
val complex_add_assoc = thm"complex_add_assoc";
val complex_add_left_commute = thm"complex_add_left_commute";
val complex_add_zero_left = thm"complex_add_zero_left";
val complex_add_zero_right = thm"complex_add_zero_right";
val complex_add_minus_right_zero = thm"complex_add_minus_right_zero";
val complex_add_minus_cancel = thm"complex_add_minus_cancel";
val complex_minus_add_cancel = thm"complex_minus_add_cancel";
val complex_add_minus_eq_minus = thm"complex_add_minus_eq_minus";
val complex_minus_add_distrib = thm"complex_minus_add_distrib";
val complex_add_left_cancel = thm"complex_add_left_cancel";
val complex_add_right_cancel = thm"complex_add_right_cancel";
val complex_eq_minus_iff = thm"complex_eq_minus_iff";
val complex_eq_minus_iff2 = thm"complex_eq_minus_iff2";
val complex_diff_0 = thm"complex_diff_0";
val complex_diff_0_right = thm"complex_diff_0_right";
val complex_diff_self = thm"complex_diff_self";
val complex_diff = thm"complex_diff";
val complex_diff_eq_eq = thm"complex_diff_eq_eq";
val complex_mult = thm"complex_mult";
val complex_mult_commute = thm"complex_mult_commute";
val complex_mult_assoc = thm"complex_mult_assoc";
val complex_mult_left_commute = thm"complex_mult_left_commute";
val complex_mult_one_left = thm"complex_mult_one_left";
val complex_mult_one_right = thm"complex_mult_one_right";
val complex_mult_zero_left = thm"complex_mult_zero_left";
val complex_mult_zero_right = thm"complex_mult_zero_right";
val complex_divide_zero = thm"complex_divide_zero";
val complex_minus_mult_eq1 = thm"complex_minus_mult_eq1";
val complex_minus_mult_eq2 = thm"complex_minus_mult_eq2";
val complex_minus_mult_commute = thm"complex_minus_mult_commute";
val complex_add_mult_distrib = thm"complex_add_mult_distrib";
val complex_add_mult_distrib2 = thm"complex_add_mult_distrib2";
val complex_zero_not_eq_one = thm"complex_zero_not_eq_one";
val complex_inverse = thm"complex_inverse";
val COMPLEX_INVERSE_ZERO = thm"COMPLEX_INVERSE_ZERO";
val COMPLEX_DIVISION_BY_ZERO = thm"COMPLEX_DIVISION_BY_ZERO";
val complex_mult_inv_left = thm"complex_mult_inv_left";
val complex_mult_inv_right = thm"complex_mult_inv_right";
val inj_complex_of_real = thm"inj_complex_of_real";
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
val inj_cnj = thm"inj_cnj";
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
val complex_add_left_cancel_zero = thm"complex_add_left_cancel_zero";
val complex_diff_mult_distrib = thm"complex_diff_mult_distrib";
val complex_diff_mult_distrib2 = thm"complex_diff_mult_distrib2";
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
val complexpow_minus = thm"complexpow_minus";
val complex_mod_inverse = thm"complex_mod_inverse";
val complex_mod_divide = thm"complex_mod_divide";
val complex_inverse_divide = thm"complex_inverse_divide";
val complexpow_i_squared = thm"complexpow_i_squared";
val complex_i_not_zero = thm"complex_i_not_zero";
val sgn_zero = thm"sgn_zero";
val sgn_one = thm"sgn_one";
val sgn_minus = thm"sgn_minus";
val sgn_eq = thm"sgn_eq";
val complex_split = thm"complex_split";
val Re_complex_i = thm"Re_complex_i";
val Im_complex_i = thm"Im_complex_i";
val i_mult_eq = thm"i_mult_eq";
val i_mult_eq2 = thm"i_mult_eq2";
val cmod_i = thm"cmod_i";
val complex_eq_Re_eq = thm"complex_eq_Re_eq";
val complex_eq_Im_eq = thm"complex_eq_Im_eq";
val complex_eq_cancel_iff = thm"complex_eq_cancel_iff";
val complex_eq_cancel_iffA = thm"complex_eq_cancel_iffA";
val complex_eq_cancel_iffB = thm"complex_eq_cancel_iffB";
val complex_eq_cancel_iffC = thm"complex_eq_cancel_iffC";
val complex_eq_cancel_iff2 = thm"complex_eq_cancel_iff2";
val complex_eq_cancel_iff2a = thm"complex_eq_cancel_iff2a";
val complex_eq_cancel_iff3 = thm"complex_eq_cancel_iff3";
val complex_eq_cancel_iff3a = thm"complex_eq_cancel_iff3a";
val complex_split_Re_zero = thm"complex_split_Re_zero";
val complex_split_Im_zero = thm"complex_split_Im_zero";
val Re_sgn = thm"Re_sgn";
val Im_sgn = thm"Im_sgn";
val complex_inverse_complex_split = thm"complex_inverse_complex_split";
val Re_mult_i_eq = thm"Re_mult_i_eq";
val Im_mult_i_eq = thm"Im_mult_i_eq";
val complex_mod_mult_i = thm"complex_mod_mult_i";
val cos_arg_i_mult_zero = thm"cos_arg_i_mult_zero";
val complex_of_real_zero_iff = thm"complex_of_real_zero_iff";
val complex_split_polar = thm"complex_split_polar";
val rcis_Ex = thm"rcis_Ex";
val Re_complex_polar = thm"Re_complex_polar";
val Re_rcis = thm"Re_rcis";
val Im_complex_polar = thm"Im_complex_polar";
val Im_rcis = thm"Im_rcis";
val complex_mod_complex_polar = thm"complex_mod_complex_polar";
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
val cis_zero2 = thm"cis_zero2";
val rcis_zero_mod = thm"rcis_zero_mod";
val rcis_zero_arg = thm"rcis_zero_arg";
val complex_of_real_minus_one = thm"complex_of_real_minus_one";
val complex_i_mult_minus = thm"complex_i_mult_minus";
val complex_i_mult_minus2 = thm"complex_i_mult_minus2";
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
val expi_Im_split = thm"expi_Im_split";
val expi_Im_cis = thm"expi_Im_cis";
val expi_add = thm"expi_add";
val expi_complex_split = thm"expi_complex_split";
val expi_zero = thm"expi_zero";
val complex_Re_mult_eq = thm"complex_Re_mult_eq";
val complex_Im_mult_eq = thm"complex_Im_mult_eq";
val complex_expi_Ex = thm"complex_expi_Ex";

val complex_add_ac = thms"complex_add_ac";
val complex_mult_ac = thms"complex_mult_ac";
*}

end



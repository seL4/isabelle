(*  Title:       NSComplex.thy
    ID:      $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header{*Nonstandard Complex Numbers*}

theory NSComplex = Complex:

constdefs
    hcomplexrel :: "((nat=>complex)*(nat=>complex)) set"
    "hcomplexrel == {p. \<exists>X Y. p = ((X::nat=>complex),Y) &
                        {n::nat. X(n) = Y(n)}: FreeUltrafilterNat}"

typedef hcomplex = "{x::nat=>complex. True}//hcomplexrel"
  by (auto simp add: quotient_def)

instance hcomplex :: zero ..
instance hcomplex :: one ..
instance hcomplex :: plus ..
instance hcomplex :: times ..
instance hcomplex :: minus ..
instance hcomplex :: inverse ..
instance hcomplex :: power ..

defs (overloaded)
  hcomplex_zero_def:
  "0 == Abs_hcomplex(hcomplexrel `` {%n. (0::complex)})"

  hcomplex_one_def:
  "1 == Abs_hcomplex(hcomplexrel `` {%n. (1::complex)})"


  hcomplex_minus_def:
  "- z == Abs_hcomplex(UN X: Rep_hcomplex(z).
                       hcomplexrel `` {%n::nat. - (X n)})"

  hcomplex_diff_def:
  "w - z == w + -(z::hcomplex)"

  hcinv_def:
  "inverse(P) == Abs_hcomplex(UN X: Rep_hcomplex(P).
                    hcomplexrel `` {%n. inverse(X n)})"

constdefs

  hcomplex_of_complex :: "complex => hcomplex"
  "hcomplex_of_complex z == Abs_hcomplex(hcomplexrel `` {%n. z})"

  (*--- real and Imaginary parts ---*)

  hRe :: "hcomplex => hypreal"
  "hRe(z) == Abs_hypreal(UN X:Rep_hcomplex(z). hyprel `` {%n. Re (X n)})"

  hIm :: "hcomplex => hypreal"
  "hIm(z) == Abs_hypreal(UN X:Rep_hcomplex(z). hyprel `` {%n. Im (X n)})"


  (*----------- modulus ------------*)

  hcmod :: "hcomplex => hypreal"
  "hcmod z == Abs_hypreal(UN X: Rep_hcomplex(z).
			  hyprel `` {%n. cmod (X n)})"

  (*------ imaginary unit ----------*)

  iii :: hcomplex
  "iii == Abs_hcomplex(hcomplexrel `` {%n. ii})"

  (*------- complex conjugate ------*)

  hcnj :: "hcomplex => hcomplex"
  "hcnj z == Abs_hcomplex(UN X:Rep_hcomplex(z). hcomplexrel `` {%n. cnj (X n)})"

  (*------------ Argand -------------*)

  hsgn :: "hcomplex => hcomplex"
  "hsgn z == Abs_hcomplex(UN X:Rep_hcomplex(z). hcomplexrel `` {%n. sgn(X n)})"

  harg :: "hcomplex => hypreal"
  "harg z == Abs_hypreal(UN X:Rep_hcomplex(z). hyprel `` {%n. arg(X n)})"

  (* abbreviation for (cos a + i sin a) *)
  hcis :: "hypreal => hcomplex"
  "hcis a == Abs_hcomplex(UN X:Rep_hypreal(a). hcomplexrel `` {%n. cis (X n)})"

  (*----- injection from hyperreals -----*)

  hcomplex_of_hypreal :: "hypreal => hcomplex"
  "hcomplex_of_hypreal r == Abs_hcomplex(UN X:Rep_hypreal(r).
			       hcomplexrel `` {%n. complex_of_real (X n)})"

  (* abbreviation for r*(cos a + i sin a) *)
  hrcis :: "[hypreal, hypreal] => hcomplex"
  "hrcis r a == hcomplex_of_hypreal r * hcis a"

  (*------------ e ^ (x + iy) ------------*)

  hexpi :: "hcomplex => hcomplex"
  "hexpi z == hcomplex_of_hypreal(( *f* exp) (hRe z)) * hcis (hIm z)"


constdefs
  HComplex :: "[hypreal,hypreal] => hcomplex"
   "HComplex x y == hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y"


defs (overloaded)

  (*----------- division ----------*)

  hcomplex_divide_def:
  "w / (z::hcomplex) == w * inverse z"

  hcomplex_add_def:
  "w + z == Abs_hcomplex(UN X:Rep_hcomplex(w). UN Y:Rep_hcomplex(z).
		      hcomplexrel `` {%n. X n + Y n})"

  hcomplex_mult_def:
  "w * z == Abs_hcomplex(UN X:Rep_hcomplex(w). UN Y:Rep_hcomplex(z).
		      hcomplexrel `` {%n. X n * Y n})"



consts
  "hcpow"  :: "[hcomplex,hypnat] => hcomplex"     (infixr 80)

defs
  (* hypernatural powers of nonstandard complex numbers *)
  hcpow_def:
  "(z::hcomplex) hcpow (n::hypnat)
      == Abs_hcomplex(UN X:Rep_hcomplex(z). UN Y: Rep_hypnat(n).
             hcomplexrel `` {%n. (X n) ^ (Y n)})"


lemma hcomplexrel_refl: "(x,x): hcomplexrel"
by (simp add: hcomplexrel_def)

lemma hcomplexrel_sym: "(x,y): hcomplexrel ==> (y,x):hcomplexrel"
by (auto simp add: hcomplexrel_def eq_commute)

lemma hcomplexrel_trans:
      "[|(x,y): hcomplexrel; (y,z):hcomplexrel|] ==> (x,z):hcomplexrel"
by (simp add: hcomplexrel_def, ultra)

lemma equiv_hcomplexrel: "equiv UNIV hcomplexrel"
apply (simp add: equiv_def refl_def sym_def trans_def hcomplexrel_refl)
apply (blast intro: hcomplexrel_sym hcomplexrel_trans)
done

lemmas equiv_hcomplexrel_iff =
    eq_equiv_class_iff [OF equiv_hcomplexrel UNIV_I UNIV_I, simp]

lemma hcomplexrel_in_hcomplex [simp]: "hcomplexrel``{x} : hcomplex"
by (simp add: hcomplex_def hcomplexrel_def quotient_def, blast)

lemma inj_on_Abs_hcomplex: "inj_on Abs_hcomplex hcomplex"
apply (rule inj_on_inverseI)
apply (erule Abs_hcomplex_inverse)
done

declare inj_on_Abs_hcomplex [THEN inj_on_iff, simp]
        Abs_hcomplex_inverse [simp]

declare equiv_hcomplexrel [THEN eq_equiv_class_iff, simp]


lemma inj_Rep_hcomplex: "inj(Rep_hcomplex)"
apply (rule inj_on_inverseI)
apply (rule Rep_hcomplex_inverse)
done

lemma lemma_hcomplexrel_refl [simp]: "x: hcomplexrel `` {x}"
by (simp add: hcomplexrel_def)

lemma hcomplex_empty_not_mem [simp]: "{} \<notin> hcomplex"
apply (simp add: hcomplex_def hcomplexrel_def)
apply (auto elim!: quotientE)
done

lemma Rep_hcomplex_nonempty [simp]: "Rep_hcomplex x \<noteq> {}"
by (cut_tac x = x in Rep_hcomplex, auto)

lemma eq_Abs_hcomplex:
    "(!!x. z = Abs_hcomplex(hcomplexrel `` {x}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_hcomplex [unfolded hcomplex_def, THEN quotientE])
apply (drule_tac f = Abs_hcomplex in arg_cong)
apply (force simp add: Rep_hcomplex_inverse hcomplexrel_def)
done

theorem hcomplex_cases [case_names Abs_hcomplex, cases type: hcomplex]:
    "(!!x. z = Abs_hcomplex(hcomplexrel``{x}) ==> P) ==> P"
by (rule eq_Abs_hcomplex [of z], blast)

lemma hcomplexrel_iff [simp]:
   "((X,Y): hcomplexrel) = ({n. X n = Y n}: FreeUltrafilterNat)"
by (simp add: hcomplexrel_def)


subsection{*Properties of Nonstandard Real and Imaginary Parts*}

lemma hRe:
     "hRe(Abs_hcomplex (hcomplexrel `` {X})) =
      Abs_hypreal(hyprel `` {%n. Re(X n)})"
apply (simp add: hRe_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hIm:
     "hIm(Abs_hcomplex (hcomplexrel `` {X})) =
      Abs_hypreal(hyprel `` {%n. Im(X n)})"
apply (simp add: hIm_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_hRe_hIm_cancel_iff:
     "(w=z) = (hRe(w) = hRe(z) & hIm(w) = hIm(z))"
apply (cases z, cases w)
apply (auto simp add: hRe hIm complex_Re_Im_cancel_iff iff: hcomplexrel_iff)
apply (ultra+)
done

lemma hcomplex_equality [intro?]: "hRe z = hRe w ==> hIm z = hIm w ==> z = w"
by (simp add: hcomplex_hRe_hIm_cancel_iff) 

lemma hcomplex_hRe_zero [simp]: "hRe 0 = 0"
by (simp add: hcomplex_zero_def hRe hypreal_zero_num)

lemma hcomplex_hIm_zero [simp]: "hIm 0 = 0"
by (simp add: hcomplex_zero_def hIm hypreal_zero_num)

lemma hcomplex_hRe_one [simp]: "hRe 1 = 1"
by (simp add: hcomplex_one_def hRe hypreal_one_num)

lemma hcomplex_hIm_one [simp]: "hIm 1 = 0"
by (simp add: hcomplex_one_def hIm hypreal_one_def hypreal_zero_num)


subsection{*Addition for Nonstandard Complex Numbers*}

lemma hcomplex_add_congruent2:
    "congruent2 hcomplexrel (%X Y. hcomplexrel `` {%n. X n + Y n})"
by (auto simp add: congruent2_def iff: hcomplexrel_iff, ultra) 

lemma hcomplex_add:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) + 
   Abs_hcomplex(hcomplexrel``{%n. Y n}) =
     Abs_hcomplex(hcomplexrel``{%n. X n + Y n})"
apply (simp add: hcomplex_add_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto simp add: iff: hcomplexrel_iff, ultra) 
done

lemma hcomplex_add_commute: "(z::hcomplex) + w = w + z"
apply (cases z, cases w)
apply (simp add: complex_add_commute hcomplex_add)
done

lemma hcomplex_add_assoc: "((z1::hcomplex) + z2) + z3 = z1 + (z2 + z3)"
apply (cases z1, cases z2, cases z3)
apply (simp add: hcomplex_add complex_add_assoc)
done

lemma hcomplex_add_zero_left: "(0::hcomplex) + z = z"
apply (cases z)
apply (simp add: hcomplex_zero_def hcomplex_add)
done

lemma hcomplex_add_zero_right: "z + (0::hcomplex) = z"
by (simp add: hcomplex_add_zero_left hcomplex_add_commute)

lemma hRe_add: "hRe(x + y) = hRe(x) + hRe(y)"
apply (cases x, cases y)
apply (simp add: hRe hcomplex_add hypreal_add complex_Re_add)
done

lemma hIm_add: "hIm(x + y) = hIm(x) + hIm(y)"
apply (cases x, cases y)
apply (simp add: hIm hcomplex_add hypreal_add complex_Im_add)
done


subsection{*Additive Inverse on Nonstandard Complex Numbers*}

lemma hcomplex_minus_congruent:
     "congruent hcomplexrel (%X. hcomplexrel `` {%n. - (X n)})"
by (simp add: congruent_def)

lemma hcomplex_minus:
  "- (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. -(X n)})"
apply (simp add: hcomplex_minus_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_add_minus_left: "-z + z = (0::hcomplex)"
apply (cases z)
apply (simp add: hcomplex_add hcomplex_minus hcomplex_zero_def)
done


subsection{*Multiplication for Nonstandard Complex Numbers*}

lemma hcomplex_mult:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) *
     Abs_hcomplex(hcomplexrel``{%n. Y n}) =
     Abs_hcomplex(hcomplexrel``{%n. X n * Y n})"
apply (simp add: hcomplex_mult_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_mult_commute: "(w::hcomplex) * z = z * w"
apply (cases w, cases z)
apply (simp add: hcomplex_mult complex_mult_commute)
done

lemma hcomplex_mult_assoc: "((u::hcomplex) * v) * w = u * (v * w)"
apply (cases u, cases v, cases w)
apply (simp add: hcomplex_mult complex_mult_assoc)
done

lemma hcomplex_mult_one_left: "(1::hcomplex) * z = z"
apply (cases z)
apply (simp add: hcomplex_one_def hcomplex_mult)
done

lemma hcomplex_mult_zero_left: "(0::hcomplex) * z = 0"
apply (cases z)
apply (simp add: hcomplex_zero_def hcomplex_mult)
done

lemma hcomplex_add_mult_distrib:
     "((z1::hcomplex) + z2) * w = (z1 * w) + (z2 * w)"
apply (cases z1, cases z2, cases w)
apply (simp add: hcomplex_mult hcomplex_add left_distrib)
done

lemma hcomplex_zero_not_eq_one: "(0::hcomplex) \<noteq> (1::hcomplex)"
by (simp add: hcomplex_zero_def hcomplex_one_def)

declare hcomplex_zero_not_eq_one [THEN not_sym, simp]


subsection{*Inverse of Nonstandard Complex Number*}

lemma hcomplex_inverse:
  "inverse (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. inverse (X n)})"
apply (simp add: hcinv_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_mult_inv_left:
      "z \<noteq> (0::hcomplex) ==> inverse(z) * z = (1::hcomplex)"
apply (cases z)
apply (simp add: hcomplex_zero_def hcomplex_one_def hcomplex_inverse hcomplex_mult, ultra)
apply (rule ccontr)
apply (drule left_inverse, auto)
done

subsection {* The Field of Nonstandard Complex Numbers *}

instance hcomplex :: field
proof
  fix z u v w :: hcomplex
  show "(u + v) + w = u + (v + w)"
    by (simp add: hcomplex_add_assoc)
  show "z + w = w + z"
    by (simp add: hcomplex_add_commute)
  show "0 + z = z"
    by (simp add: hcomplex_add_zero_left)
  show "-z + z = 0"
    by (simp add: hcomplex_add_minus_left)
  show "z - w = z + -w"
    by (simp add: hcomplex_diff_def)
  show "(u * v) * w = u * (v * w)"
    by (simp add: hcomplex_mult_assoc)
  show "z * w = w * z"
    by (simp add: hcomplex_mult_commute)
  show "1 * z = z"
    by (simp add: hcomplex_mult_one_left)
  show "0 \<noteq> (1::hcomplex)"
    by (rule hcomplex_zero_not_eq_one)
  show "(u + v) * w = u * w + v * w"
    by (simp add: hcomplex_add_mult_distrib)
  show "z / w = z * inverse w"
    by (simp add: hcomplex_divide_def)
  assume "w \<noteq> 0"
  thus "inverse w * w = 1"
    by (rule hcomplex_mult_inv_left)
qed

instance hcomplex :: division_by_zero
proof
  show "inverse 0 = (0::hcomplex)"
    by (simp add: hcomplex_inverse hcomplex_zero_def)
qed


subsection{*More Minus Laws*}

lemma hRe_minus: "hRe(-z) = - hRe(z)"
apply (cases z)
apply (simp add: hRe hcomplex_minus hypreal_minus complex_Re_minus)
done

lemma hIm_minus: "hIm(-z) = - hIm(z)"
apply (cases z)
apply (simp add: hIm hcomplex_minus hypreal_minus complex_Im_minus)
done

lemma hcomplex_add_minus_eq_minus:
      "x + y = (0::hcomplex) ==> x = -y"
apply (drule Ring_and_Field.equals_zero_I)
apply (simp add: minus_equation_iff [of x y])
done

lemma hcomplex_i_mult_eq [simp]: "iii * iii = - 1"
by (simp add: iii_def hcomplex_mult hcomplex_one_def hcomplex_minus)

lemma hcomplex_i_mult_left [simp]: "iii * (iii * z) = -z"
by (simp add: mult_assoc [symmetric])

lemma hcomplex_i_not_zero [simp]: "iii \<noteq> 0"
by (simp add: iii_def hcomplex_zero_def)


subsection{*More Multiplication Laws*}

lemma hcomplex_mult_one_right: "z * (1::hcomplex) = z"
by (rule Ring_and_Field.mult_1_right)

lemma hcomplex_mult_minus_one [simp]: "- 1 * (z::hcomplex) = -z"
by simp

lemma hcomplex_mult_minus_one_right [simp]: "(z::hcomplex) * - 1 = -z"
by (subst hcomplex_mult_commute, simp)

lemma hcomplex_mult_left_cancel:
     "(c::hcomplex) \<noteq> (0::hcomplex) ==> (c*a=c*b) = (a=b)"
by (simp add: field_mult_cancel_left)

lemma hcomplex_mult_right_cancel:
     "(c::hcomplex) \<noteq> (0::hcomplex) ==> (a*c=b*c) = (a=b)"
by (simp add: Ring_and_Field.field_mult_cancel_right)


subsection{*Subraction and Division*}

lemma hcomplex_diff:
 "Abs_hcomplex(hcomplexrel``{%n. X n}) - Abs_hcomplex(hcomplexrel``{%n. Y n}) =
  Abs_hcomplex(hcomplexrel``{%n. X n - Y n})"
by (simp add: hcomplex_diff_def hcomplex_minus hcomplex_add complex_diff_def)

lemma hcomplex_diff_eq_eq [simp]: "((x::hcomplex) - y = z) = (x = z + y)"
by (rule Ring_and_Field.diff_eq_eq)

lemma hcomplex_add_divide_distrib: "(x+y)/(z::hcomplex) = x/z + y/z"
by (rule Ring_and_Field.add_divide_distrib)


subsection{*Embedding Properties for @{term hcomplex_of_hypreal} Map*}

lemma hcomplex_of_hypreal:
  "hcomplex_of_hypreal (Abs_hypreal(hyprel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. complex_of_real (X n)})"
apply (simp add: hcomplex_of_hypreal_def)
apply (rule_tac f = Abs_hcomplex in arg_cong, auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_of_hypreal_cancel_iff [iff]:
     "(hcomplex_of_hypreal x = hcomplex_of_hypreal y) = (x = y)"
apply (cases x, cases y)
apply (simp add: hcomplex_of_hypreal)
done

lemma hcomplex_of_hypreal_minus:
     "hcomplex_of_hypreal(-x) = - hcomplex_of_hypreal x"
apply (cases x)
apply (simp add: hcomplex_of_hypreal hcomplex_minus hypreal_minus complex_of_real_minus)
done

lemma hcomplex_of_hypreal_inverse:
     "hcomplex_of_hypreal(inverse x) = inverse(hcomplex_of_hypreal x)"
apply (cases x)
apply (simp add: hcomplex_of_hypreal hypreal_inverse hcomplex_inverse complex_of_real_inverse)
done

lemma hcomplex_of_hypreal_add:
     "hcomplex_of_hypreal x + hcomplex_of_hypreal y =
      hcomplex_of_hypreal (x + y)"
apply (cases x, cases y)
apply (simp add: hcomplex_of_hypreal hypreal_add hcomplex_add complex_of_real_add)
done

lemma hcomplex_of_hypreal_diff:
     "hcomplex_of_hypreal x - hcomplex_of_hypreal y =
      hcomplex_of_hypreal (x - y)"
by (simp add: hcomplex_diff_def hcomplex_of_hypreal_minus [symmetric] hcomplex_of_hypreal_add hypreal_diff_def)

lemma hcomplex_of_hypreal_mult:
     "hcomplex_of_hypreal x * hcomplex_of_hypreal y =
      hcomplex_of_hypreal (x * y)"
apply (cases x, cases y)
apply (simp add: hcomplex_of_hypreal hypreal_mult hcomplex_mult complex_of_real_mult)
done

lemma hcomplex_of_hypreal_divide:
  "hcomplex_of_hypreal x / hcomplex_of_hypreal y = hcomplex_of_hypreal(x/y)"
apply (simp add: hcomplex_divide_def)
apply (case_tac "y=0", simp)
apply (auto simp add: hcomplex_of_hypreal_mult hcomplex_of_hypreal_inverse [symmetric])
apply (simp add: hypreal_divide_def)
done

lemma hcomplex_of_hypreal_one [simp]: "hcomplex_of_hypreal 1 = 1"
by (simp add: hcomplex_one_def hcomplex_of_hypreal hypreal_one_num)

lemma hcomplex_of_hypreal_zero [simp]: "hcomplex_of_hypreal 0 = 0"
by (simp add: hcomplex_zero_def hypreal_zero_def hcomplex_of_hypreal)

lemma hRe_hcomplex_of_hypreal [simp]: "hRe(hcomplex_of_hypreal z) = z"
apply (cases z)
apply (auto simp add: hcomplex_of_hypreal hRe)
done

lemma hIm_hcomplex_of_hypreal [simp]: "hIm(hcomplex_of_hypreal z) = 0"
apply (cases z)
apply (auto simp add: hcomplex_of_hypreal hIm hypreal_zero_num)
done

lemma hcomplex_of_hypreal_epsilon_not_zero [simp]:
     "hcomplex_of_hypreal epsilon \<noteq> 0"
by (auto simp add: hcomplex_of_hypreal epsilon_def hcomplex_zero_def)


subsection{*HComplex theorems*}

lemma hRe_HComplex [simp]: "hRe (HComplex x y) = x"
apply (cases x, cases y)
apply (simp add: HComplex_def hRe iii_def hcomplex_add hcomplex_mult hcomplex_of_hypreal)
done

lemma hIm_HComplex [simp]: "hIm (HComplex x y) = y"
apply (cases x, cases y)
apply (simp add: HComplex_def hIm iii_def hcomplex_add hcomplex_mult hcomplex_of_hypreal)
done

text{*Relates the two nonstandard constructions*}
lemma HComplex_eq_Abs_hcomplex_Complex:
     "HComplex (Abs_hypreal (hyprel `` {X})) (Abs_hypreal (hyprel `` {Y})) =
      Abs_hcomplex(hcomplexrel `` {%n::nat. Complex (X n) (Y n)})";
by (simp add: hcomplex_hRe_hIm_cancel_iff hRe hIm) 

lemma hcomplex_surj [simp]: "HComplex (hRe z) (hIm z) = z"
by (simp add: hcomplex_equality) 

lemma hcomplex_induct [case_names rect, induct type: hcomplex]:
     "(\<And>x y. P (HComplex x y)) ==> P z"
by (rule hcomplex_surj [THEN subst], blast)


subsection{*Modulus (Absolute Value) of Nonstandard Complex Number*}

lemma hcmod:
  "hcmod (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hypreal(hyprel `` {%n. cmod (X n)})"

apply (simp add: hcmod_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcmod_zero [simp]: "hcmod(0) = 0"
by (simp add: hcomplex_zero_def hypreal_zero_def hcmod)

lemma hcmod_one [simp]: "hcmod(1) = 1"
by (simp add: hcomplex_one_def hcmod hypreal_one_num)

lemma hcmod_hcomplex_of_hypreal [simp]: "hcmod(hcomplex_of_hypreal x) = abs x"
apply (cases x)
apply (auto simp add: hcmod hcomplex_of_hypreal hypreal_hrabs)
done

lemma hcomplex_of_hypreal_abs:
     "hcomplex_of_hypreal (abs x) =
      hcomplex_of_hypreal(hcmod(hcomplex_of_hypreal x))"
by simp

lemma HComplex_inject [simp]: "HComplex x y = HComplex x' y' = (x=x' & y=y')"
apply (rule iffI) 
 prefer 2 apply simp 
apply (simp add: HComplex_def iii_def) 
apply (cases x, cases y, cases x', cases y')
apply (auto simp add: iii_def hcomplex_mult hcomplex_add hcomplex_of_hypreal)
apply (ultra+) 
done

lemma HComplex_add [simp]:
     "HComplex x1 y1 + HComplex x2 y2 = HComplex (x1+x2) (y1+y2)"
by (simp add: HComplex_def hcomplex_of_hypreal_add [symmetric] add_ac right_distrib) 

lemma HComplex_minus [simp]: "- HComplex x y = HComplex (-x) (-y)"
by (simp add: HComplex_def hcomplex_of_hypreal_minus) 

lemma HComplex_diff [simp]:
     "HComplex x1 y1 - HComplex x2 y2 = HComplex (x1-x2) (y1-y2)"
by (simp add: diff_minus)

lemma HComplex_mult [simp]:
  "HComplex x1 y1 * HComplex x2 y2 = HComplex (x1*x2 - y1*y2) (x1*y2 + y1*x2)"
by (simp add: HComplex_def diff_minus hcomplex_of_hypreal_minus 
       hcomplex_of_hypreal_add [symmetric] hcomplex_of_hypreal_mult [symmetric]
       add_ac mult_ac right_distrib)

(*HComplex_inverse is proved below*)

lemma hcomplex_of_hypreal_eq: "hcomplex_of_hypreal r = HComplex r 0"
by (simp add: HComplex_def)

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
     "iii * hcomplex_of_hypreal r = HComplex 0 r"
by (simp add: HComplex_def)

lemma hcomplex_of_hypreal_i [simp]:
     "hcomplex_of_hypreal r * iii = HComplex 0 r"
by (simp add: mult_commute) 


subsection{*Conjugation*}

lemma hcnj:
  "hcnj (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
   Abs_hcomplex(hcomplexrel `` {%n. cnj(X n)})"
apply (simp add: hcnj_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_hcnj_cancel_iff [iff]: "(hcnj x = hcnj y) = (x = y)"
apply (cases x, cases y)
apply (simp add: hcnj)
done

lemma hcomplex_hcnj_hcnj [simp]: "hcnj (hcnj z) = z"
apply (cases z)
apply (simp add: hcnj)
done

lemma hcomplex_hcnj_hcomplex_of_hypreal [simp]:
     "hcnj (hcomplex_of_hypreal x) = hcomplex_of_hypreal x"
apply (cases x)
apply (simp add: hcnj hcomplex_of_hypreal)
done

lemma hcomplex_hmod_hcnj [simp]: "hcmod (hcnj z) = hcmod z"
apply (cases z)
apply (simp add: hcnj hcmod)
done

lemma hcomplex_hcnj_minus: "hcnj (-z) = - hcnj z"
apply (cases z)
apply (simp add: hcnj hcomplex_minus complex_cnj_minus)
done

lemma hcomplex_hcnj_inverse: "hcnj(inverse z) = inverse(hcnj z)"
apply (cases z)
apply (simp add: hcnj hcomplex_inverse complex_cnj_inverse)
done

lemma hcomplex_hcnj_add: "hcnj(w + z) = hcnj(w) + hcnj(z)"
apply (cases z, cases w)
apply (simp add: hcnj hcomplex_add complex_cnj_add)
done

lemma hcomplex_hcnj_diff: "hcnj(w - z) = hcnj(w) - hcnj(z)"
apply (cases z, cases w)
apply (simp add: hcnj hcomplex_diff complex_cnj_diff)
done

lemma hcomplex_hcnj_mult: "hcnj(w * z) = hcnj(w) * hcnj(z)"
apply (cases z, cases w)
apply (simp add: hcnj hcomplex_mult complex_cnj_mult)
done

lemma hcomplex_hcnj_divide: "hcnj(w / z) = (hcnj w)/(hcnj z)"
by (simp add: hcomplex_divide_def hcomplex_hcnj_mult hcomplex_hcnj_inverse)

lemma hcnj_one [simp]: "hcnj 1 = 1"
by (simp add: hcomplex_one_def hcnj)

lemma hcomplex_hcnj_zero [simp]: "hcnj 0 = 0"
by (simp add: hcomplex_zero_def hcnj)

lemma hcomplex_hcnj_zero_iff [iff]: "(hcnj z = 0) = (z = 0)"
apply (cases z)
apply (simp add: hcomplex_zero_def hcnj)
done

lemma hcomplex_mult_hcnj:
     "z * hcnj z = hcomplex_of_hypreal (hRe(z) ^ 2 + hIm(z) ^ 2)"
apply (cases z)
apply (simp add: hcnj hcomplex_mult hcomplex_of_hypreal hRe hIm hypreal_add
                      hypreal_mult complex_mult_cnj numeral_2_eq_2)
done


subsection{*More Theorems about the Function @{term hcmod}*}

lemma hcomplex_hcmod_eq_zero_cancel [simp]: "(hcmod x = 0) = (x = 0)"
apply (cases x)
apply (simp add: hcmod hcomplex_zero_def hypreal_zero_num)
done

lemma hcmod_hcomplex_of_hypreal_of_nat [simp]:
     "hcmod (hcomplex_of_hypreal(hypreal_of_nat n)) = hypreal_of_nat n"
apply (simp add: abs_if linorder_not_less)
done

lemma hcmod_hcomplex_of_hypreal_of_hypnat [simp]:
     "hcmod (hcomplex_of_hypreal(hypreal_of_hypnat n)) = hypreal_of_hypnat n"
apply (simp add: abs_if linorder_not_less)
done

lemma hcmod_minus [simp]: "hcmod (-x) = hcmod(x)"
apply (cases x)
apply (simp add: hcmod hcomplex_minus)
done

lemma hcmod_mult_hcnj: "hcmod(z * hcnj(z)) = hcmod(z) ^ 2"
apply (cases z)
apply (simp add: hcmod hcomplex_mult hcnj hypreal_mult complex_mod_mult_cnj numeral_2_eq_2)
done

lemma hcmod_ge_zero [simp]: "(0::hypreal) \<le> hcmod x"
apply (cases x)
apply (simp add: hcmod hypreal_zero_num hypreal_le)
done

lemma hrabs_hcmod_cancel [simp]: "abs(hcmod x) = hcmod x"
by (simp add: abs_if linorder_not_less)

lemma hcmod_mult: "hcmod(x*y) = hcmod(x) * hcmod(y)"
apply (cases x, cases y)
apply (simp add: hcmod hcomplex_mult hypreal_mult complex_mod_mult)
done

lemma hcmod_add_squared_eq:
     "hcmod(x + y) ^ 2 = hcmod(x) ^ 2 + hcmod(y) ^ 2 + 2 * hRe(x * hcnj y)"
apply (cases x, cases y)
apply (simp add: hcmod hcomplex_add hypreal_mult hRe hcnj hcomplex_mult
                      numeral_2_eq_2 realpow_two [symmetric]
                  del: realpow_Suc)
apply (simp add: numeral_2_eq_2 [symmetric] complex_mod_add_squared_eq
                 hypreal_add [symmetric] hypreal_mult [symmetric]
                 hypreal_of_real_def [symmetric])
done

lemma hcomplex_hRe_mult_hcnj_le_hcmod [simp]: "hRe(x * hcnj y) \<le> hcmod(x * hcnj y)"
apply (cases x, cases y)
apply (simp add: hcmod hcnj hcomplex_mult hRe hypreal_le)
done

lemma hcomplex_hRe_mult_hcnj_le_hcmod2 [simp]: "hRe(x * hcnj y) \<le> hcmod(x * y)"
apply (cut_tac x = x and y = y in hcomplex_hRe_mult_hcnj_le_hcmod)
apply (simp add: hcmod_mult)
done

lemma hcmod_triangle_squared [simp]: "hcmod (x + y) ^ 2 \<le> (hcmod(x) + hcmod(y)) ^ 2"
apply (cases x, cases y)
apply (simp add: hcmod hcnj hcomplex_add hypreal_mult hypreal_add
                      hypreal_le realpow_two [symmetric] numeral_2_eq_2
            del: realpow_Suc)
apply (simp add: numeral_2_eq_2 [symmetric])
done

lemma hcmod_triangle_ineq [simp]: "hcmod (x + y) \<le> hcmod(x) + hcmod(y)"
apply (cases x, cases y)
apply (simp add: hcmod hcomplex_add hypreal_add hypreal_le)
done

lemma hcmod_triangle_ineq2 [simp]: "hcmod(b + a) - hcmod b \<le> hcmod a"
apply (cut_tac x1 = b and y1 = a and c = "-hcmod b" in hcmod_triangle_ineq [THEN add_right_mono])
apply (simp add: add_ac)
done

lemma hcmod_diff_commute: "hcmod (x - y) = hcmod (y - x)"
apply (cases x, cases y)
apply (simp add: hcmod hcomplex_diff complex_mod_diff_commute)
done

lemma hcmod_add_less:
     "[| hcmod x < r; hcmod y < s |] ==> hcmod (x + y) < r + s"
apply (cases x, cases y, cases r, cases s)
apply (simp add: hcmod hcomplex_add hypreal_add hypreal_less, ultra)
apply (auto intro: complex_mod_add_less)
done

lemma hcmod_mult_less:
     "[| hcmod x < r; hcmod y < s |] ==> hcmod (x * y) < r * s"
apply (cases x, cases y, cases r, cases s)
apply (simp add: hcmod hypreal_mult hypreal_less hcomplex_mult, ultra)
apply (auto intro: complex_mod_mult_less)
done

lemma hcmod_diff_ineq [simp]: "hcmod(a) - hcmod(b) \<le> hcmod(a + b)"
apply (cases a, cases b)
apply (simp add: hcmod hcomplex_add hypreal_diff hypreal_le)
done


subsection{*A Few Nonlinear Theorems*}

lemma hcpow:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) hcpow
   Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hcomplex(hcomplexrel``{%n. X n ^ Y n})"
apply (simp add: hcpow_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hcomplex_of_hypreal_hyperpow:
     "hcomplex_of_hypreal (x pow n) = (hcomplex_of_hypreal x) hcpow n"
apply (cases x, cases n)
apply (simp add: hcomplex_of_hypreal hyperpow hcpow complex_of_real_pow)
done

lemma hcmod_hcpow: "hcmod(x hcpow n) = hcmod(x) pow n"
apply (cases x, cases n)
apply (simp add: hcpow hyperpow hcmod complex_mod_complexpow)
done

lemma hcmod_hcomplex_inverse: "hcmod(inverse x) = inverse(hcmod x)"
apply (case_tac "x = 0", simp)
apply (rule_tac c1 = "hcmod x" in hypreal_mult_left_cancel [THEN iffD1])
apply (auto simp add: hcmod_mult [symmetric])
done

lemma hcmod_divide: "hcmod(x/y) = hcmod(x)/(hcmod y)"
by (simp add: hcomplex_divide_def hypreal_divide_def hcmod_mult hcmod_hcomplex_inverse)


subsection{*Exponentiation*}

primrec
     hcomplexpow_0:   "z ^ 0       = 1"
     hcomplexpow_Suc: "z ^ (Suc n) = (z::hcomplex) * (z ^ n)"

instance hcomplex :: ringpower
proof
  fix z :: hcomplex
  fix n :: nat
  show "z^0 = 1" by simp
  show "z^(Suc n) = z * (z^n)" by simp
qed

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
     "(-x::hcomplex) hcpow n =
      (if ( *pNat* even) n then (x hcpow n) else -(x hcpow n))"
apply (cases x, cases n)
apply (auto simp add: hcpow hyperpow starPNat hcomplex_minus, ultra)
apply (auto simp add: neg_power_if, ultra)
done

lemma hcpow_mult: "((r::hcomplex) * s) hcpow n = (r hcpow n) * (s hcpow n)"
apply (cases r, cases s, cases n)
apply (simp add: hcpow hypreal_mult hcomplex_mult power_mult_distrib)
done

lemma hcpow_zero [simp]: "0 hcpow (n + 1) = 0"
apply (simp add: hcomplex_zero_def hypnat_one_def, cases n)
apply (simp add: hcpow hypnat_add)
done

lemma hcpow_zero2 [simp]: "0 hcpow (hSuc n) = 0"
by (simp add: hSuc_def)

lemma hcpow_not_zero [simp,intro]: "r \<noteq> 0 ==> r hcpow n \<noteq> (0::hcomplex)"
apply (cases r, cases n)
apply (auto simp add: hcpow hcomplex_zero_def, ultra)
done

lemma hcpow_zero_zero: "r hcpow n = (0::hcomplex) ==> r = 0"
by (blast intro: ccontr dest: hcpow_not_zero)

lemma hcomplex_divide:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) / Abs_hcomplex(hcomplexrel``{%n. Y n}) =
   Abs_hcomplex(hcomplexrel``{%n. X n / Y n})"
by (simp add: hcomplex_divide_def complex_divide_def hcomplex_inverse hcomplex_mult)




subsection{*The Function @{term hsgn}*}

lemma hsgn:
  "hsgn (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. sgn (X n)})"
apply (simp add: hsgn_def)
apply (rule_tac f = Abs_hcomplex in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma hsgn_zero [simp]: "hsgn 0 = 0"
by (simp add: hcomplex_zero_def hsgn)

lemma hsgn_one [simp]: "hsgn 1 = 1"
by (simp add: hcomplex_one_def hsgn)

lemma hsgn_minus: "hsgn (-z) = - hsgn(z)"
apply (cases z)
apply (simp add: hsgn hcomplex_minus sgn_minus)
done

lemma hsgn_eq: "hsgn z = z / hcomplex_of_hypreal (hcmod z)"
apply (cases z)
apply (simp add: hsgn hcomplex_divide hcomplex_of_hypreal hcmod sgn_eq)
done


lemma hcmod_i: "hcmod (HComplex x y) = ( *f* sqrt) (x ^ 2 + y ^ 2)"
apply (cases x, cases y) 
apply (simp add: HComplex_eq_Abs_hcomplex_Complex starfun 
                 hypreal_mult hypreal_add hcmod numeral_2_eq_2)
done

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

lemma hRe_hsgn [simp]: "hRe(hsgn z) = hRe(z)/hcmod z"
apply (cases z)
apply (simp add: hsgn hcmod hRe hypreal_divide)
done

lemma hIm_hsgn [simp]: "hIm(hsgn z) = hIm(z)/hcmod z"
apply (cases z)
apply (simp add: hsgn hcmod hIm hypreal_divide)
done

lemma real_two_squares_add_zero_iff [simp]: "(x*x + y*y = 0) = ((x::real) = 0 & y = 0)"
by (auto intro: real_sum_squares_cancel)

lemma hcomplex_inverse_complex_split:
     "inverse(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y) =
      hcomplex_of_hypreal(x/(x ^ 2 + y ^ 2)) -
      iii * hcomplex_of_hypreal(y/(x ^ 2 + y ^ 2))"
apply (cases x, cases y)
apply (simp add: hcomplex_of_hypreal hcomplex_mult hcomplex_add iii_def starfun hypreal_mult hypreal_add hcomplex_inverse hypreal_divide hcomplex_diff complex_inverse_complex_split numeral_2_eq_2)
apply (simp add: diff_minus) 
done

lemma HComplex_inverse:
     "inverse (HComplex x y) =
      HComplex (x/(x ^ 2 + y ^ 2)) (-y/(x ^ 2 + y ^ 2))"
by (simp only: HComplex_def hcomplex_inverse_complex_split, simp)



lemma hRe_mult_i_eq[simp]:
    "hRe (iii * hcomplex_of_hypreal y) = 0"
apply (simp add: iii_def, cases y)
apply (simp add: hcomplex_of_hypreal hcomplex_mult hRe hypreal_zero_num)
done

lemma hIm_mult_i_eq [simp]:
    "hIm (iii * hcomplex_of_hypreal y) = y"
apply (simp add: iii_def, cases y)
apply (simp add: hcomplex_of_hypreal hcomplex_mult hIm hypreal_zero_num)
done

lemma hcmod_mult_i [simp]: "hcmod (iii * hcomplex_of_hypreal y) = abs y"
apply (cases y)
apply (simp add: hcomplex_of_hypreal hcmod hypreal_hrabs iii_def hcomplex_mult)
done

lemma hcmod_mult_i2 [simp]: "hcmod (hcomplex_of_hypreal y * iii) = abs y"
by (simp only: hcmod_mult_i hcomplex_mult_commute)

(*---------------------------------------------------------------------------*)
(*  harg                                                                     *)
(*---------------------------------------------------------------------------*)

lemma harg:
  "harg (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hypreal(hyprel `` {%n. arg (X n)})"
apply (simp add: harg_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto iff: hcomplexrel_iff, ultra)
done

lemma cos_harg_i_mult_zero_pos:
     "0 < y ==> ( *f* cos) (harg(HComplex 0 y)) = 0"
apply (cases y)
apply (simp add: HComplex_def hcomplex_of_hypreal iii_def hcomplex_mult
                hcomplex_add hypreal_zero_num hypreal_less starfun harg, ultra)
done

lemma cos_harg_i_mult_zero_neg:
     "y < 0 ==> ( *f* cos) (harg(HComplex 0 y)) = 0"
apply (cases y)
apply (simp add: HComplex_def hcomplex_of_hypreal iii_def hcomplex_mult
                 hcomplex_add hypreal_zero_num hypreal_less starfun harg, ultra)
done

lemma cos_harg_i_mult_zero [simp]:
     "y \<noteq> 0 ==> ( *f* cos) (harg(HComplex 0 y)) = 0"
by (auto simp add: linorder_neq_iff
                   cos_harg_i_mult_zero_pos cos_harg_i_mult_zero_neg)

lemma hcomplex_of_hypreal_zero_iff [simp]:
     "(hcomplex_of_hypreal y = 0) = (y = 0)"
apply (cases y)
apply (simp add: hcomplex_of_hypreal hypreal_zero_num hcomplex_zero_def)
done


subsection{*Polar Form for Nonstandard Complex Numbers*}

lemma complex_split_polar2:
     "\<forall>n. \<exists>r a. (z n) =  complex_of_real r * (Complex (cos a) (sin a))"
by (blast intro: complex_split_polar)

lemma lemma_hypreal_P_EX2:
     "(\<exists>(x::hypreal) y. P x y) =
      (\<exists>f g. P (Abs_hypreal(hyprel `` {f})) (Abs_hypreal(hyprel `` {g})))"
apply auto
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal, auto)
done

lemma hcomplex_split_polar:
  "\<exists>r a. z = hcomplex_of_hypreal r * (HComplex(( *f* cos) a)(( *f* sin) a))"
apply (cases z)
apply (simp add: lemma_hypreal_P_EX2 hcomplex_of_hypreal iii_def starfun hcomplex_add hcomplex_mult HComplex_def)
apply (cut_tac z = x in complex_split_polar2)
apply (drule choice, safe)+
apply (rule_tac x = f in exI)
apply (rule_tac x = fa in exI, auto)
done

lemma hcis:
  "hcis (Abs_hypreal(hyprel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. cis (X n)})"
apply (simp add: hcis_def)
apply (rule_tac f = Abs_hcomplex in arg_cong, auto iff: hcomplexrel_iff, ultra)
done

lemma hcis_eq:
   "hcis a =
    (hcomplex_of_hypreal(( *f* cos) a) +
    iii * hcomplex_of_hypreal(( *f* sin) a))"
apply (cases a)
apply (simp add: starfun hcis hcomplex_of_hypreal iii_def hcomplex_mult hcomplex_add cis_def)
done

lemma hrcis:
  "hrcis (Abs_hypreal(hyprel `` {%n. X n})) (Abs_hypreal(hyprel `` {%n. Y n})) =
      Abs_hcomplex(hcomplexrel `` {%n. rcis (X n) (Y n)})"
by (simp add: hrcis_def hcomplex_of_hypreal hcomplex_mult hcis rcis_def)

lemma hrcis_Ex: "\<exists>r a. z = hrcis r a"
apply (simp add: hrcis_def hcis_eq hcomplex_of_hypreal_mult_HComplex [symmetric])
apply (rule hcomplex_split_polar)
done

lemma hRe_hcomplex_polar [simp]:
     "hRe (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = 
      r * ( *f* cos) a"
by (simp add: hcomplex_of_hypreal_mult_HComplex)

lemma hRe_hrcis [simp]: "hRe(hrcis r a) = r * ( *f* cos) a"
by (simp add: hrcis_def hcis_eq)

lemma hIm_hcomplex_polar [simp]:
     "hIm (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) = 
      r * ( *f* sin) a"
by (simp add: hcomplex_of_hypreal_mult_HComplex)

lemma hIm_hrcis [simp]: "hIm(hrcis r a) = r * ( *f* sin) a"
by (simp add: hrcis_def hcis_eq)


lemma hcmod_unit_one [simp]:
     "hcmod (HComplex (( *f* cos) a) (( *f* sin) a)) = 1"
apply (cases a) 
apply (simp add: HComplex_def iii_def starfun hcomplex_of_hypreal 
                 hcomplex_mult hcmod hcomplex_add hypreal_one_def)
done

lemma hcmod_complex_polar [simp]:
     "hcmod (hcomplex_of_hypreal r * HComplex (( *f* cos) a) (( *f* sin) a)) =
      abs r"
apply (simp only: hcmod_mult hcmod_unit_one, simp)  
done

lemma hcmod_hrcis [simp]: "hcmod(hrcis r a) = abs r"
by (simp add: hrcis_def hcis_eq)

(*---------------------------------------------------------------------------*)
(*  (r1 * hrcis a) * (r2 * hrcis b) = r1 * r2 * hrcis (a + b)                *)
(*---------------------------------------------------------------------------*)

lemma hcis_hrcis_eq: "hcis a = hrcis 1 a"
by (simp add: hrcis_def)
declare hcis_hrcis_eq [symmetric, simp]

lemma hrcis_mult:
  "hrcis r1 a * hrcis r2 b = hrcis (r1*r2) (a + b)"
apply (simp add: hrcis_def, cases r1, cases r2, cases a, cases b)
apply (simp add: hrcis hcis hypreal_add hypreal_mult hcomplex_of_hypreal
                      hcomplex_mult cis_mult [symmetric]
                      complex_of_real_mult [symmetric])
done

lemma hcis_mult: "hcis a * hcis b = hcis (a + b)"
apply (cases a, cases b)
apply (simp add: hcis hcomplex_mult hypreal_add cis_mult)
done

lemma hcis_zero [simp]: "hcis 0 = 1"
by (simp add: hcomplex_one_def hcis hypreal_zero_num)

lemma hrcis_zero_mod [simp]: "hrcis 0 a = 0"
apply (simp add: hcomplex_zero_def, cases a)
apply (simp add: hrcis hypreal_zero_num)
done

lemma hrcis_zero_arg [simp]: "hrcis r 0 = hcomplex_of_hypreal r"
apply (cases r)
apply (simp add: hrcis hypreal_zero_num hcomplex_of_hypreal)
done

lemma hcomplex_i_mult_minus [simp]: "iii * (iii * x) = - x"
by (simp add: hcomplex_mult_assoc [symmetric])

lemma hcomplex_i_mult_minus2 [simp]: "iii * iii * x = - x"
by simp

lemma hcis_hypreal_of_nat_Suc_mult:
   "hcis (hypreal_of_nat (Suc n) * a) = hcis a * hcis (hypreal_of_nat n * a)"
apply (cases a)
apply (simp add: hypreal_of_nat hcis hypreal_mult hcomplex_mult cis_real_of_nat_Suc_mult)
done

lemma NSDeMoivre: "(hcis a) ^ n = hcis (hypreal_of_nat n * a)"
apply (induct_tac "n")
apply (simp_all add: hcis_hypreal_of_nat_Suc_mult)
done

lemma hcis_hypreal_of_hypnat_Suc_mult:
     "hcis (hypreal_of_hypnat (n + 1) * a) =
      hcis a * hcis (hypreal_of_hypnat n * a)"
apply (cases a, cases n)
apply (simp add: hcis hypreal_of_hypnat hypnat_add hypnat_one_def hypreal_mult hcomplex_mult cis_real_of_nat_Suc_mult)
done

lemma NSDeMoivre_ext: "(hcis a) hcpow n = hcis (hypreal_of_hypnat n * a)"
apply (cases a, cases n)
apply (simp add: hcis hypreal_of_hypnat hypreal_mult hcpow DeMoivre)
done

lemma DeMoivre2:
  "(hrcis r a) ^ n = hrcis (r ^ n) (hypreal_of_nat n * a)"
apply (simp add: hrcis_def power_mult_distrib NSDeMoivre hcomplex_of_hypreal_pow)
done

lemma DeMoivre2_ext:
  "(hrcis r a) hcpow n = hrcis (r pow n) (hypreal_of_hypnat n * a)"
apply (simp add: hrcis_def hcpow_mult NSDeMoivre_ext hcomplex_of_hypreal_hyperpow)
done

lemma hcis_inverse [simp]: "inverse(hcis a) = hcis (-a)"
apply (cases a)
apply (simp add: hcomplex_inverse hcis hypreal_minus)
done

lemma hrcis_inverse: "inverse(hrcis r a) = hrcis (inverse r) (-a)"
apply (cases a, cases r)
apply (simp add: hcomplex_inverse hrcis hypreal_minus hypreal_inverse rcis_inverse, ultra)
apply (simp add: real_divide_def)
done

lemma hRe_hcis [simp]: "hRe(hcis a) = ( *f* cos) a"
apply (cases a)
apply (simp add: hcis starfun hRe)
done

lemma hIm_hcis [simp]: "hIm(hcis a) = ( *f* sin) a"
apply (cases a)
apply (simp add: hcis starfun hIm)
done

lemma cos_n_hRe_hcis_pow_n: "( *f* cos) (hypreal_of_nat n * a) = hRe(hcis a ^ n)"
by (simp add: NSDeMoivre)

lemma sin_n_hIm_hcis_pow_n: "( *f* sin) (hypreal_of_nat n * a) = hIm(hcis a ^ n)"
by (simp add: NSDeMoivre)

lemma cos_n_hRe_hcis_hcpow_n: "( *f* cos) (hypreal_of_hypnat n * a) = hRe(hcis a hcpow n)"
by (simp add: NSDeMoivre_ext)

lemma sin_n_hIm_hcis_hcpow_n: "( *f* sin) (hypreal_of_hypnat n * a) = hIm(hcis a hcpow n)"
by (simp add: NSDeMoivre_ext)

lemma hexpi_add: "hexpi(a + b) = hexpi(a) * hexpi(b)"
apply (simp add: hexpi_def, cases a, cases b)
apply (simp add: hcis hRe hIm hcomplex_add hcomplex_mult hypreal_mult starfun hcomplex_of_hypreal cis_mult [symmetric] complex_Im_add complex_Re_add exp_add complex_of_real_mult)
done


subsection{*@{term hcomplex_of_complex}: the Injection from
  type @{typ complex} to to @{typ hcomplex}*}

lemma inj_hcomplex_of_complex: "inj(hcomplex_of_complex)"
apply (rule inj_onI, rule ccontr)
apply (simp add: hcomplex_of_complex_def)
done

lemma hcomplex_of_complex_i: "iii = hcomplex_of_complex ii"
by (simp add: iii_def hcomplex_of_complex_def)

lemma hcomplex_of_complex_add [simp]:
     "hcomplex_of_complex (z1 + z2) = hcomplex_of_complex z1 + hcomplex_of_complex z2"
by (simp add: hcomplex_of_complex_def hcomplex_add)

lemma hcomplex_of_complex_mult [simp]:
     "hcomplex_of_complex (z1 * z2) = hcomplex_of_complex z1 * hcomplex_of_complex z2"
by (simp add: hcomplex_of_complex_def hcomplex_mult)

lemma hcomplex_of_complex_eq_iff [simp]:
     "(hcomplex_of_complex z1 = hcomplex_of_complex z2) = (z1 = z2)"
by (simp add: hcomplex_of_complex_def)


lemma hcomplex_of_complex_minus [simp]:
     "hcomplex_of_complex (-r) = - hcomplex_of_complex  r"
by (simp add: hcomplex_of_complex_def hcomplex_minus)

lemma hcomplex_of_complex_one [simp]: "hcomplex_of_complex 1 = 1"
by (simp add: hcomplex_of_complex_def hcomplex_one_def)

lemma hcomplex_of_complex_zero [simp]: "hcomplex_of_complex 0 = 0"
by (simp add: hcomplex_of_complex_def hcomplex_zero_def)

lemma hcomplex_of_complex_zero_iff [simp]:
     "(hcomplex_of_complex r = 0) = (r = 0)"
by (auto intro: FreeUltrafilterNat_P 
         simp add: hcomplex_of_complex_def hcomplex_zero_def)

lemma hcomplex_of_complex_inverse [simp]:
     "hcomplex_of_complex (inverse r) = inverse (hcomplex_of_complex r)"
apply (case_tac "r=0")
apply (simp add: hcomplex_of_complex_zero)
apply (rule_tac c1 = "hcomplex_of_complex r"
       in hcomplex_mult_left_cancel [THEN iffD1])
apply (force simp add: hcomplex_of_complex_zero_iff)
apply (subst hcomplex_of_complex_mult [symmetric])
apply (simp add: hcomplex_of_complex_one hcomplex_of_complex_zero_iff)
done

lemma hcomplex_of_complex_divide [simp]:
     "hcomplex_of_complex (z1 / z2) = hcomplex_of_complex z1 / hcomplex_of_complex z2"
by (simp add: hcomplex_divide_def complex_divide_def)

lemma hRe_hcomplex_of_complex:
   "hRe (hcomplex_of_complex z) = hypreal_of_real (Re z)"
by (simp add: hcomplex_of_complex_def hypreal_of_real_def hRe)

lemma hIm_hcomplex_of_complex:
   "hIm (hcomplex_of_complex z) = hypreal_of_real (Im z)"
by (simp add: hcomplex_of_complex_def hypreal_of_real_def hIm)

lemma hcmod_hcomplex_of_complex:
     "hcmod (hcomplex_of_complex x) = hypreal_of_real (cmod x)"
by (simp add: hypreal_of_real_def hcomplex_of_complex_def hcmod)


subsection{*Numerals and Arithmetic*}

instance hcomplex :: number ..

primrec (*the type constraint is essential!*)
  number_of_Pls: "number_of bin.Pls = 0"
  number_of_Min: "number_of bin.Min = - (1::hcomplex)"
  number_of_BIT: "number_of(w BIT x) = (if x then 1 else 0) +
	                               (number_of w) + (number_of w)"

declare number_of_Pls [simp del]
        number_of_Min [simp del]
        number_of_BIT [simp del]

instance hcomplex :: number_ring
proof
  show "Numeral0 = (0::hcomplex)" by (rule number_of_Pls)
  show "-1 = - (1::hcomplex)" by (rule number_of_Min)
  fix w :: bin and x :: bool
  show "(number_of (w BIT x) :: hcomplex) =
        (if x then 1 else 0) + number_of w + number_of w"
    by (rule number_of_BIT)
qed


text{*Collapse applications of @{term hcomplex_of_complex} to @{term number_of}*}
lemma hcomplex_number_of [simp]:
     "hcomplex_of_complex (number_of w) = number_of w"
apply (induct w) 
apply (simp_all only: number_of hcomplex_of_complex_add 
                      hcomplex_of_complex_minus, simp_all) 
done

lemma hcomplex_of_hypreal_eq_hcomplex_of_complex: 
     "hcomplex_of_hypreal (hypreal_of_real x) =  
      hcomplex_of_complex(complex_of_real x)"
by (simp add: hypreal_of_real_def hcomplex_of_hypreal hcomplex_of_complex_def 
              complex_of_real_def)

lemma hcomplex_hypreal_number_of: 
  "hcomplex_of_complex (number_of w) = hcomplex_of_hypreal(number_of w)"
by (simp only: complex_number_of [symmetric] hypreal_number_of [symmetric] 
               hcomplex_of_hypreal_eq_hcomplex_of_complex)

text{*This theorem is necessary because theorems such as
   @{text iszero_number_of_0} only hold for ordered rings. They cannot
   be generalized to fields in general because they fail for finite fields.
   They work for type complex because the reals can be embedded in them.*}
lemma iszero_hcomplex_number_of [simp]:
     "iszero (number_of w :: hcomplex) = iszero (number_of w :: real)"
apply (simp only: iszero_complex_number_of [symmetric])  
apply (simp only: hcomplex_of_complex_zero_iff hcomplex_number_of [symmetric] 
                  iszero_def)  
done


(*
Goal "z + hcnj z =  
      hcomplex_of_hypreal (2 * hRe(z))"
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),HOL_ss addsimps [hRe,hcnj,hcomplex_add,
    hypreal_mult,hcomplex_of_hypreal,complex_add_cnj]));
qed "hcomplex_add_hcnj";

Goal "z - hcnj z = \
\     hcomplex_of_hypreal (hypreal_of_real #2 * hIm(z)) * iii";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcnj,hcomplex_diff,
    hypreal_of_real_def,hypreal_mult,hcomplex_of_hypreal,
    complex_diff_cnj,iii_def,hcomplex_mult]));
qed "hcomplex_diff_hcnj";
*)


lemma hcomplex_hcnj_num_zero_iff: "(hcnj z = 0) = (z = 0)"
apply (auto simp add: hcomplex_hcnj_zero_iff)
done
declare hcomplex_hcnj_num_zero_iff [simp]

lemma hcomplex_zero_num: "0 = Abs_hcomplex (hcomplexrel `` {%n. 0})"
apply (simp add: hcomplex_zero_def)
done

lemma hcomplex_one_num: "1 =  Abs_hcomplex (hcomplexrel `` {%n. 1})"
apply (simp add: hcomplex_one_def)
done

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
by (simp only: hcomplex_number_of [symmetric] hcomplex_hypreal_number_of
               hcomplex_hcnj_hcomplex_of_hypreal)

lemma hcomplex_number_of_hcmod [simp]: 
      "hcmod(number_of v :: hcomplex) = abs (number_of v :: hypreal)"
by (simp only: hcomplex_number_of [symmetric] hcomplex_hypreal_number_of
               hcmod_hcomplex_of_hypreal)

lemma hcomplex_number_of_hRe [simp]: 
      "hRe(number_of v :: hcomplex) = number_of v"
by (simp only: hcomplex_number_of [symmetric] hcomplex_hypreal_number_of
               hRe_hcomplex_of_hypreal)

lemma hcomplex_number_of_hIm [simp]: 
      "hIm(number_of v :: hcomplex) = 0"
by (simp only: hcomplex_number_of [symmetric] hcomplex_hypreal_number_of
               hIm_hcomplex_of_hypreal)


ML
{*
val hcomplex_zero_def = thm"hcomplex_zero_def";
val hcomplex_one_def = thm"hcomplex_one_def";
val hcomplex_minus_def = thm"hcomplex_minus_def";
val hcomplex_diff_def = thm"hcomplex_diff_def";
val hcomplex_divide_def = thm"hcomplex_divide_def";
val hcomplex_mult_def = thm"hcomplex_mult_def";
val hcomplex_add_def = thm"hcomplex_add_def";
val hcomplex_of_complex_def = thm"hcomplex_of_complex_def";
val iii_def = thm"iii_def";

val hcomplexrel_iff = thm"hcomplexrel_iff";
val hcomplexrel_refl = thm"hcomplexrel_refl";
val hcomplexrel_sym = thm"hcomplexrel_sym";
val hcomplexrel_trans = thm"hcomplexrel_trans";
val equiv_hcomplexrel = thm"equiv_hcomplexrel";
val equiv_hcomplexrel_iff = thm"equiv_hcomplexrel_iff";
val hcomplexrel_in_hcomplex = thm"hcomplexrel_in_hcomplex";
val inj_on_Abs_hcomplex = thm"inj_on_Abs_hcomplex";
val inj_Rep_hcomplex = thm"inj_Rep_hcomplex";
val lemma_hcomplexrel_refl = thm"lemma_hcomplexrel_refl";
val hcomplex_empty_not_mem = thm"hcomplex_empty_not_mem";
val Rep_hcomplex_nonempty = thm"Rep_hcomplex_nonempty";
val eq_Abs_hcomplex = thm"eq_Abs_hcomplex";
val hRe = thm"hRe";
val hIm = thm"hIm";
val hcomplex_hRe_hIm_cancel_iff = thm"hcomplex_hRe_hIm_cancel_iff";
val hcomplex_hRe_zero = thm"hcomplex_hRe_zero";
val hcomplex_hIm_zero = thm"hcomplex_hIm_zero";
val hcomplex_hRe_one = thm"hcomplex_hRe_one";
val hcomplex_hIm_one = thm"hcomplex_hIm_one";
val inj_hcomplex_of_complex = thm"inj_hcomplex_of_complex";
val hcomplex_of_complex_i = thm"hcomplex_of_complex_i";
val hcomplex_add_congruent2 = thm"hcomplex_add_congruent2";
val hcomplex_add = thm"hcomplex_add";
val hcomplex_add_commute = thm"hcomplex_add_commute";
val hcomplex_add_assoc = thm"hcomplex_add_assoc";
val hcomplex_add_zero_left = thm"hcomplex_add_zero_left";
val hcomplex_add_zero_right = thm"hcomplex_add_zero_right";
val hRe_add = thm"hRe_add";
val hIm_add = thm"hIm_add";
val hcomplex_minus_congruent = thm"hcomplex_minus_congruent";
val hcomplex_minus = thm"hcomplex_minus";
val hcomplex_add_minus_left = thm"hcomplex_add_minus_left";
val hRe_minus = thm"hRe_minus";
val hIm_minus = thm"hIm_minus";
val hcomplex_add_minus_eq_minus = thm"hcomplex_add_minus_eq_minus";
val hcomplex_diff = thm"hcomplex_diff";
val hcomplex_diff_eq_eq = thm"hcomplex_diff_eq_eq";
val hcomplex_mult = thm"hcomplex_mult";
val hcomplex_mult_commute = thm"hcomplex_mult_commute";
val hcomplex_mult_assoc = thm"hcomplex_mult_assoc";
val hcomplex_mult_one_left = thm"hcomplex_mult_one_left";
val hcomplex_mult_one_right = thm"hcomplex_mult_one_right";
val hcomplex_mult_zero_left = thm"hcomplex_mult_zero_left";
val hcomplex_mult_minus_one = thm"hcomplex_mult_minus_one";
val hcomplex_mult_minus_one_right = thm"hcomplex_mult_minus_one_right";
val hcomplex_add_mult_distrib = thm"hcomplex_add_mult_distrib";
val hcomplex_zero_not_eq_one = thm"hcomplex_zero_not_eq_one";
val hcomplex_inverse = thm"hcomplex_inverse";
val hcomplex_mult_inv_left = thm"hcomplex_mult_inv_left";
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
val hcomplex_divide = thm"hcomplex_divide";
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
val hcomplex_of_complex_add = thm"hcomplex_of_complex_add";
val hcomplex_of_complex_mult = thm"hcomplex_of_complex_mult";
val hcomplex_of_complex_eq_iff = thm"hcomplex_of_complex_eq_iff";
val hcomplex_of_complex_minus = thm"hcomplex_of_complex_minus";
val hcomplex_of_complex_one = thm"hcomplex_of_complex_one";
val hcomplex_of_complex_zero = thm"hcomplex_of_complex_zero";
val hcomplex_of_complex_zero_iff = thm"hcomplex_of_complex_zero_iff";
val hcomplex_of_complex_inverse = thm"hcomplex_of_complex_inverse";
val hcomplex_of_complex_divide = thm"hcomplex_of_complex_divide";
val hRe_hcomplex_of_complex = thm"hRe_hcomplex_of_complex";
val hIm_hcomplex_of_complex = thm"hIm_hcomplex_of_complex";
val hcmod_hcomplex_of_complex = thm"hcmod_hcomplex_of_complex";
*}

end

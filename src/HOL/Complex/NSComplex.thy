(*  Title:       NSComplex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Nonstandard Complex numbers
*)

theory NSComplex = NSInduct:

(*for Ring_and_Field?*)
declare field_mult_eq_0_iff [simp]

(* Move to one of the hyperreal theories *)
lemma hypreal_of_nat: "hypreal_of_nat m = Abs_hypreal(hyprel `` {%n. real m})"
apply (induct_tac "m")
apply (auto simp add: hypreal_zero_def hypreal_of_nat_Suc hypreal_zero_num hypreal_one_num hypreal_add real_of_nat_Suc)
done

(* not proved already? strange! *)
lemma hypreal_of_nat_le_iff:
      "(hypreal_of_nat n <= hypreal_of_nat m) = (n <= m)"
apply (unfold hypreal_le_def)
apply auto
done
declare hypreal_of_nat_le_iff [simp]

lemma hypreal_of_nat_ge_zero: "0 <= hypreal_of_nat n"
apply (simp (no_asm) add: hypreal_of_nat_zero [symmetric] 
         del: hypreal_of_nat_zero)
done
declare hypreal_of_nat_ge_zero [simp]

declare hypreal_of_nat_ge_zero [THEN hrabs_eqI1, simp]

lemma hypreal_of_hypnat_ge_zero: "0 <= hypreal_of_hypnat n"
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (simp (no_asm_simp) add: hypreal_of_hypnat hypreal_zero_num hypreal_le)
done
declare hypreal_of_hypnat_ge_zero [simp]
declare hypreal_of_hypnat_ge_zero [THEN hrabs_eqI1, simp]

constdefs
    hcomplexrel :: "((nat=>complex)*(nat=>complex)) set"
    "hcomplexrel == {p. EX X Y. p = ((X::nat=>complex),Y) &
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

constdefs

  hcomplex_of_complex :: "complex => hcomplex"
  "hcomplex_of_complex z == Abs_hcomplex(hcomplexrel `` {%n. z})"

  hcinv  :: "hcomplex => hcomplex"
  "inverse(P)   == Abs_hcomplex(UN X: Rep_hcomplex(P).
                    hcomplexrel `` {%n. inverse(X n)})"

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

  (* abbreviation for r*(cos a + i sin a) *)
  hrcis :: "[hypreal, hypreal] => hcomplex"
  "hrcis r a == hcomplex_of_hypreal r * hcis a"

  (*----- injection from hyperreals -----*)

  hcomplex_of_hypreal :: "hypreal => hcomplex"
  "hcomplex_of_hypreal r == Abs_hcomplex(UN X:Rep_hypreal(r).
			       hcomplexrel `` {%n. complex_of_real (X n)})"

  (*------------ e ^ (x + iy) ------------*)

  hexpi :: "hcomplex => hcomplex"
  "hexpi z == hcomplex_of_hypreal(( *f* exp) (hRe z)) * hcis (hIm z)"


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


primrec
     hcomplexpow_0:   "z ^ 0       = 1"
     hcomplexpow_Suc: "z ^ (Suc n) = (z::hcomplex) * (z ^ n)"


consts
  "hcpow"  :: "[hcomplex,hypnat] => hcomplex"     (infixr 80)

defs
  (* hypernatural powers of nonstandard complex numbers *)
  hcpow_def:
  "(z::hcomplex) hcpow (n::hypnat)
      == Abs_hcomplex(UN X:Rep_hcomplex(z). UN Y: Rep_hypnat(n).
             hcomplexrel `` {%n. (X n) ^ (Y n)})"


lemma hcomplexrel_iff:
   "((X,Y): hcomplexrel) = ({n. X n = Y n}: FreeUltrafilterNat)"
apply (unfold hcomplexrel_def)
apply fast
done

lemma hcomplexrel_refl: "(x,x): hcomplexrel"
apply (simp add: hcomplexrel_iff) 
done

lemma hcomplexrel_sym: "(x,y): hcomplexrel ==> (y,x):hcomplexrel"
apply (auto simp add: hcomplexrel_iff eq_commute)
done

lemma hcomplexrel_trans:
      "[|(x,y): hcomplexrel; (y,z):hcomplexrel|] ==> (x,z):hcomplexrel"
apply (simp add: hcomplexrel_iff) 
apply ultra
done

lemma equiv_hcomplexrel: "equiv UNIV hcomplexrel"
apply (simp add: equiv_def refl_def sym_def trans_def hcomplexrel_refl) 
apply (blast intro: hcomplexrel_sym hcomplexrel_trans) 
done

lemmas equiv_hcomplexrel_iff =
    eq_equiv_class_iff [OF equiv_hcomplexrel UNIV_I UNIV_I, simp]

lemma hcomplexrel_in_hcomplex [simp]: "hcomplexrel``{x} : hcomplex"
apply (unfold hcomplex_def hcomplexrel_def quotient_def)
apply blast
done

lemma inj_on_Abs_hcomplex: "inj_on Abs_hcomplex hcomplex"
apply (rule inj_on_inverseI)
apply (erule Abs_hcomplex_inverse)
done

declare inj_on_Abs_hcomplex [THEN inj_on_iff, simp]
        Abs_hcomplex_inverse [simp]

declare equiv_hcomplexrel [THEN eq_equiv_class_iff, simp]

declare hcomplexrel_iff [iff]

lemma inj_Rep_hcomplex: "inj(Rep_hcomplex)"
apply (rule inj_on_inverseI)
apply (rule Rep_hcomplex_inverse)
done

lemma lemma_hcomplexrel_refl: "x: hcomplexrel `` {x}"
apply (unfold hcomplexrel_def)
apply (safe)
apply auto
done
declare lemma_hcomplexrel_refl [simp]

lemma hcomplex_empty_not_mem: "{} ~: hcomplex"
apply (unfold hcomplex_def)
apply (auto elim!: quotientE)
done
declare hcomplex_empty_not_mem [simp]

lemma Rep_hcomplex_nonempty: "Rep_hcomplex x ~= {}"
apply (cut_tac x = "x" in Rep_hcomplex)
apply auto
done
declare Rep_hcomplex_nonempty [simp]

lemma eq_Abs_hcomplex:
    "(!!x. z = Abs_hcomplex(hcomplexrel `` {x}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_hcomplex [unfolded hcomplex_def, THEN quotientE])
apply (drule_tac f = Abs_hcomplex in arg_cong)
apply (force simp add: Rep_hcomplex_inverse)
done


subsection{*Properties of Nonstandard Real and Imaginary Parts*}

lemma hRe:
     "hRe(Abs_hcomplex (hcomplexrel `` {X})) =
      Abs_hypreal(hyprel `` {%n. Re(X n)})"
apply (unfold hRe_def)
apply (rule_tac f = "Abs_hypreal" in arg_cong)
apply (auto , ultra)
done

lemma hIm:
     "hIm(Abs_hcomplex (hcomplexrel `` {X})) =
      Abs_hypreal(hyprel `` {%n. Im(X n)})"
apply (unfold hIm_def)
apply (rule_tac f = "Abs_hypreal" in arg_cong)
apply (auto , ultra)
done

lemma hcomplex_hRe_hIm_cancel_iff:
     "(w=z) = (hRe(w) = hRe(z) & hIm(w) = hIm(z))"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (auto simp add: hRe hIm complex_Re_Im_cancel_iff)
apply (ultra+)
done

lemma hcomplex_hRe_zero: "hRe 0 = 0"
apply (unfold hcomplex_zero_def)
apply (simp (no_asm) add: hRe hypreal_zero_num)
done
declare hcomplex_hRe_zero [simp]

lemma hcomplex_hIm_zero: "hIm 0 = 0"
apply (unfold hcomplex_zero_def)
apply (simp (no_asm) add: hIm hypreal_zero_num)
done
declare hcomplex_hIm_zero [simp]

lemma hcomplex_hRe_one: "hRe 1 = 1"
apply (unfold hcomplex_one_def)
apply (simp (no_asm) add: hRe hypreal_one_num)
done
declare hcomplex_hRe_one [simp]

lemma hcomplex_hIm_one: "hIm 1 = 0"
apply (unfold hcomplex_one_def)
apply (simp (no_asm) add: hIm hypreal_one_def hypreal_zero_num)
done
declare hcomplex_hIm_one [simp]

(*-----------------------------------------------------------------------*)
(*   hcomplex_of_complex: the injection from complex to hcomplex         *)
(* ----------------------------------------------------------------------*)

lemma inj_hcomplex_of_complex: "inj(hcomplex_of_complex)"
apply (rule inj_onI , rule ccontr)
apply (auto simp add: hcomplex_of_complex_def)
done

lemma hcomplex_of_complex_i: "iii = hcomplex_of_complex ii"
apply (unfold iii_def hcomplex_of_complex_def)
apply (simp (no_asm))
done

(*-----------------------------------------------------------------------*)
(*   Addition for nonstandard complex numbers: hcomplex_add              *)
(* ----------------------------------------------------------------------*)

lemma hcomplex_add_congruent2:
    "congruent2 hcomplexrel (%X Y. hcomplexrel `` {%n. X n + Y n})"
apply (unfold congruent2_def)
apply safe
apply (ultra+)
done

lemma hcomplex_add:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) + Abs_hcomplex(hcomplexrel``{%n. Y n}) =
   Abs_hcomplex(hcomplexrel``{%n. X n + Y n})"
apply (unfold hcomplex_add_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma hcomplex_add_commute: "(z::hcomplex) + w = w + z"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (simp add: complex_add_commute hcomplex_add)
done

lemma hcomplex_add_assoc: "((z1::hcomplex) + z2) + z3 = z1 + (z2 + z3)"
apply (rule_tac z = "z1" in eq_Abs_hcomplex)
apply (rule_tac z = "z2" in eq_Abs_hcomplex)
apply (rule_tac z = "z3" in eq_Abs_hcomplex)
apply (simp add: hcomplex_add complex_add_assoc)
done

lemma hcomplex_add_zero_left: "(0::hcomplex) + z = z"
apply (unfold hcomplex_zero_def)
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (simp add: hcomplex_add)
done

lemma hcomplex_add_zero_right: "z + (0::hcomplex) = z"
apply (simp add: hcomplex_add_zero_left hcomplex_add_commute)
done

lemma hRe_add: "hRe(x + y) = hRe(x) + hRe(y)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hRe hcomplex_add hypreal_add complex_Re_add)
done

lemma hIm_add: "hIm(x + y) = hIm(x) + hIm(y)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hIm hcomplex_add hypreal_add complex_Im_add)
done

(*-----------------------------------------------------------------------*)
(* hypreal_minus: additive inverse on nonstandard complex                *)
(* ----------------------------------------------------------------------*)

lemma hcomplex_minus_congruent:
  "congruent hcomplexrel (%X. hcomplexrel `` {%n. - (X n)})"
apply (unfold congruent_def)
apply safe
apply (ultra+)
done

lemma hcomplex_minus:
  "- (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. -(X n)})"
apply (unfold hcomplex_minus_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma hcomplex_add_minus_left: "-z + z = (0::hcomplex)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_add hcomplex_minus hcomplex_zero_def)
done


subsection{*Multiplication for Nonstandard Complex Numbers*}

lemma hcomplex_mult:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) * 
     Abs_hcomplex(hcomplexrel``{%n. Y n}) =
   Abs_hcomplex(hcomplexrel``{%n. X n * Y n})"
apply (unfold hcomplex_mult_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma hcomplex_mult_commute: "(w::hcomplex) * z = z * w"
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_mult complex_mult_commute)
done

lemma hcomplex_mult_assoc: "((u::hcomplex) * v) * w = u * (v * w)"
apply (rule_tac z = "u" in eq_Abs_hcomplex)
apply (rule_tac z = "v" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_mult complex_mult_assoc)
done

lemma hcomplex_mult_one_left: "(1::hcomplex) * z = z"
apply (unfold hcomplex_one_def)
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_mult)
done

lemma hcomplex_mult_zero_left: "(0::hcomplex) * z = 0"
apply (unfold hcomplex_zero_def)
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_mult)
done

lemma hcomplex_add_mult_distrib:
     "((z1::hcomplex) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule_tac z = "z1" in eq_Abs_hcomplex)
apply (rule_tac z = "z2" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_mult hcomplex_add complex_add_mult_distrib)
done

lemma hcomplex_zero_not_eq_one: "(0::hcomplex) ~= (1::hcomplex)"
apply (unfold hcomplex_zero_def hcomplex_one_def)
apply auto
done
declare hcomplex_zero_not_eq_one [simp]
declare hcomplex_zero_not_eq_one [THEN not_sym, simp]


subsection{*Inverse of Nonstandard Complex Number*}

lemma hcomplex_inverse:
  "inverse (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. inverse (X n)})"
apply (unfold hcinv_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma hcomplex_mult_inv_left:
      "z ~= (0::hcomplex) ==> inverse(z) * z = (1::hcomplex)"
apply (unfold hcomplex_zero_def hcomplex_one_def)
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_inverse hcomplex_mult)
apply (ultra)
apply (rule ccontr)
apply (drule complex_mult_inv_left)
apply auto
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
  assume neq: "w \<noteq> 0"
  thus "z / w = z * inverse w"
    by (simp add: hcomplex_divide_def)
  show "inverse w * w = 1"
    by (rule hcomplex_mult_inv_left)
qed

lemma HCOMPLEX_INVERSE_ZERO: "inverse (0::hcomplex) = 0"
apply (simp add:  hcomplex_zero_def hcomplex_inverse)
done

lemma HCOMPLEX_DIVISION_BY_ZERO: "a / (0::hcomplex) = 0"
apply (simp add: hcomplex_divide_def HCOMPLEX_INVERSE_ZERO)
done

instance hcomplex :: division_by_zero
proof
  fix x :: hcomplex
  show "inverse 0 = (0::hcomplex)" by (rule HCOMPLEX_INVERSE_ZERO)
  show "x/0 = 0" by (rule HCOMPLEX_DIVISION_BY_ZERO) 
qed

subsection{*More Minus Laws*}

lemma inj_hcomplex_minus: "inj(%z::hcomplex. -z)"
apply (rule inj_onI)
apply (drule_tac f = "uminus" in arg_cong)
apply simp
done

lemma hRe_minus: "hRe(-z) = - hRe(z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hRe hcomplex_minus hypreal_minus complex_Re_minus)
done

lemma hIm_minus: "hIm(-z) = - hIm(z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hIm hcomplex_minus hypreal_minus complex_Im_minus)
done

lemma hcomplex_add_minus_eq_minus:
      "x + y = (0::hcomplex) ==> x = -y"
apply (drule Ring_and_Field.equals_zero_I) 
apply (simp add: minus_equation_iff [of x y]) 
done


subsection{*More Multiplication Laws*}

lemma hcomplex_mult_one_right: "z * (1::hcomplex) = z"
apply (rule Ring_and_Field.mult_1_right)
done

lemma hcomplex_mult_minus_one: "- 1 * (z::hcomplex) = -z"
apply (simp (no_asm))
done
declare hcomplex_mult_minus_one [simp]

lemma hcomplex_mult_minus_one_right: "(z::hcomplex) * - 1 = -z"
apply (subst hcomplex_mult_commute)
apply (simp (no_asm))
done
declare hcomplex_mult_minus_one_right [simp]

lemma hcomplex_mult_left_cancel:
     "(c::hcomplex) ~= (0::hcomplex) ==> (c*a=c*b) = (a=b)"
by (simp add: field_mult_cancel_left) 

lemma hcomplex_mult_right_cancel:
     "(c::hcomplex) ~= (0::hcomplex) ==> (a*c=b*c) = (a=b)"
apply (simp add: Ring_and_Field.field_mult_cancel_right); 
done


subsection{*Subraction and Division*}

lemma hcomplex_diff:
 "Abs_hcomplex(hcomplexrel``{%n. X n}) - Abs_hcomplex(hcomplexrel``{%n. Y n}) =
  Abs_hcomplex(hcomplexrel``{%n. X n - Y n})"
apply (unfold hcomplex_diff_def)
apply (auto simp add: hcomplex_minus hcomplex_add complex_diff_def)
done

lemma hcomplex_diff_eq_eq: "((x::hcomplex) - y = z) = (x = z + y)"
apply (rule Ring_and_Field.diff_eq_eq) 
done

lemma hcomplex_add_divide_distrib: "(x+y)/(z::hcomplex) = x/z + y/z"
apply (rule Ring_and_Field.add_divide_distrib) 
done


subsection{*Embedding Properties for @{term hcomplex_of_hypreal} Map*}

lemma hcomplex_of_hypreal:
  "hcomplex_of_hypreal (Abs_hypreal(hyprel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. complex_of_real (X n)})"
apply (unfold hcomplex_of_hypreal_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply auto
apply (ultra)
done

lemma inj_hcomplex_of_hypreal: "inj hcomplex_of_hypreal"
apply (rule inj_onI)
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal)
done

lemma hcomplex_of_hypreal_cancel_iff:
     "(hcomplex_of_hypreal x = hcomplex_of_hypreal y) = (x = y)"
apply (auto dest: inj_hcomplex_of_hypreal [THEN injD])
done
declare hcomplex_of_hypreal_cancel_iff [iff]

lemma hcomplex_of_hypreal_minus:
     "hcomplex_of_hypreal(-x) = - hcomplex_of_hypreal x"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcomplex_minus hypreal_minus complex_of_real_minus)
done

lemma hcomplex_of_hypreal_inverse:
     "hcomplex_of_hypreal(inverse x) = inverse(hcomplex_of_hypreal x)"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hypreal_inverse hcomplex_inverse complex_of_real_inverse)
done

lemma hcomplex_of_hypreal_add:
     "hcomplex_of_hypreal x + hcomplex_of_hypreal y =
      hcomplex_of_hypreal (x + y)"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hypreal_add hcomplex_add complex_of_real_add)
done

lemma hcomplex_of_hypreal_diff:
     "hcomplex_of_hypreal x - hcomplex_of_hypreal y =
      hcomplex_of_hypreal (x - y)"
apply (unfold hcomplex_diff_def)
apply (auto simp add: hcomplex_of_hypreal_minus [symmetric] hcomplex_of_hypreal_add hypreal_diff_def)
done

lemma hcomplex_of_hypreal_mult:
     "hcomplex_of_hypreal x * hcomplex_of_hypreal y =
      hcomplex_of_hypreal (x * y)"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hypreal_mult hcomplex_mult 
                      complex_of_real_mult)
done

lemma hcomplex_of_hypreal_divide:
  "hcomplex_of_hypreal x / hcomplex_of_hypreal y = hcomplex_of_hypreal(x/y)"
apply (unfold hcomplex_divide_def)
apply (case_tac "y=0")
apply (simp)
apply (auto simp add: hcomplex_of_hypreal_mult hcomplex_of_hypreal_inverse [symmetric])
apply (simp (no_asm) add: hypreal_divide_def)
done

lemma hcomplex_of_hypreal_one [simp]:
      "hcomplex_of_hypreal 1 = 1"
apply (unfold hcomplex_one_def)
apply (auto simp add: hcomplex_of_hypreal hypreal_one_num)
done

lemma hcomplex_of_hypreal_zero [simp]:
      "hcomplex_of_hypreal 0 = 0"
apply (unfold hcomplex_zero_def hypreal_zero_def)
apply (auto simp add: hcomplex_of_hypreal)
done

lemma hcomplex_of_hypreal_pow:
     "hcomplex_of_hypreal (x ^ n) = (hcomplex_of_hypreal x) ^ n"
apply (induct_tac "n")
apply (auto simp add: hcomplex_of_hypreal_mult [symmetric])
done

lemma hRe_hcomplex_of_hypreal: "hRe(hcomplex_of_hypreal z) = z"
apply (rule_tac z = "z" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hRe)
done
declare hRe_hcomplex_of_hypreal [simp]

lemma hIm_hcomplex_of_hypreal: "hIm(hcomplex_of_hypreal z) = 0"
apply (rule_tac z = "z" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hIm hypreal_zero_num)
done
declare hIm_hcomplex_of_hypreal [simp]

lemma hcomplex_of_hypreal_epsilon_not_zero: "hcomplex_of_hypreal epsilon ~= 0"
apply (auto simp add: hcomplex_of_hypreal epsilon_def hcomplex_zero_def)
done
declare hcomplex_of_hypreal_epsilon_not_zero [simp]


subsection{*Modulus (Absolute Value) of Nonstandard Complex Number*}

lemma hcmod:
  "hcmod (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hypreal(hyprel `` {%n. cmod (X n)})"

apply (unfold hcmod_def)
apply (rule_tac f = "Abs_hypreal" in arg_cong)
apply (auto, ultra)
done

lemma hcmod_zero [simp]:
      "hcmod(0) = 0"
apply (unfold hcomplex_zero_def hypreal_zero_def)
apply (auto simp add: hcmod)
done

lemma hcmod_one:
      "hcmod(1) = 1"
apply (unfold hcomplex_one_def)
apply (auto simp add: hcmod hypreal_one_num)
done
declare hcmod_one [simp]

lemma hcmod_hcomplex_of_hypreal: "hcmod(hcomplex_of_hypreal x) = abs x"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (auto simp add: hcmod hcomplex_of_hypreal hypreal_hrabs)
done
declare hcmod_hcomplex_of_hypreal [simp]

lemma hcomplex_of_hypreal_abs:
     "hcomplex_of_hypreal (abs x) =
      hcomplex_of_hypreal(hcmod(hcomplex_of_hypreal x))"
apply (simp (no_asm))
done


subsection{*Conjugation*}

lemma hcnj:
  "hcnj (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
   Abs_hcomplex(hcomplexrel `` {%n. cnj(X n)})"
apply (unfold hcnj_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma inj_hcnj: "inj hcnj"
apply (rule inj_onI)
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcnj)
done

lemma hcomplex_hcnj_cancel_iff: "(hcnj x = hcnj y) = (x = y)"
apply (auto dest: inj_hcnj [THEN injD])
done
declare hcomplex_hcnj_cancel_iff [simp]

lemma hcomplex_hcnj_hcnj: "hcnj (hcnj z) = z"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcnj)
done
declare hcomplex_hcnj_hcnj [simp]

lemma hcomplex_hcnj_hcomplex_of_hypreal:
     "hcnj (hcomplex_of_hypreal x) = hcomplex_of_hypreal x"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (auto simp add: hcnj hcomplex_of_hypreal)
done
declare hcomplex_hcnj_hcomplex_of_hypreal [simp]

lemma hcomplex_hmod_hcnj: "hcmod (hcnj z) = hcmod z"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcmod)
done
declare hcomplex_hmod_hcnj [simp]

lemma hcomplex_hcnj_minus: "hcnj (-z) = - hcnj z"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcomplex_minus complex_cnj_minus)
done

lemma hcomplex_hcnj_inverse: "hcnj(inverse z) = inverse(hcnj z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcomplex_inverse complex_cnj_inverse)
done

lemma hcomplex_hcnj_add: "hcnj(w + z) = hcnj(w) + hcnj(z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcomplex_add complex_cnj_add)
done

lemma hcomplex_hcnj_diff: "hcnj(w - z) = hcnj(w) - hcnj(z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcomplex_diff complex_cnj_diff)
done

lemma hcomplex_hcnj_mult: "hcnj(w * z) = hcnj(w) * hcnj(z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (rule_tac z = "w" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcomplex_mult complex_cnj_mult)
done

lemma hcomplex_hcnj_divide: "hcnj(w / z) = (hcnj w)/(hcnj z)"
apply (unfold hcomplex_divide_def)
apply (simp (no_asm) add: hcomplex_hcnj_mult hcomplex_hcnj_inverse)
done

lemma hcnj_one: "hcnj 1 = 1"
apply (unfold hcomplex_one_def)
apply (simp (no_asm) add: hcnj)
done
declare hcnj_one [simp]

lemma hcomplex_hcnj_pow: "hcnj(z ^ n) = hcnj(z) ^ n"
apply (induct_tac "n")
apply (auto simp add: hcomplex_hcnj_mult)
done

(* MOVE to NSComplexBin
Goal "z + hcnj z =
      hcomplex_of_hypreal (2 * hRe(z))"
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),HOL_ss addsimps [hRe,hcnj,hcomplex_add,
    hypreal_mult,hcomplex_of_hypreal,complex_add_cnj]));
qed "hcomplex_add_hcnj";

Goal "z - hcnj z = \
\     hcomplex_of_hypreal (hypreal_of_real 2 * hIm(z)) * iii";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcnj,hcomplex_diff,
    hypreal_of_real_def,hypreal_mult,hcomplex_of_hypreal,
    complex_diff_cnj,iii_def,hcomplex_mult]));
qed "hcomplex_diff_hcnj";
*)

lemma hcomplex_hcnj_zero:
      "hcnj 0 = 0"
apply (unfold hcomplex_zero_def)
apply (auto simp add: hcnj)
done
declare hcomplex_hcnj_zero [simp]

lemma hcomplex_hcnj_zero_iff: "(hcnj z = 0) = (z = 0)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_zero_def hcnj)
done
declare hcomplex_hcnj_zero_iff [iff]

lemma hcomplex_mult_hcnj:
     "z * hcnj z = hcomplex_of_hypreal (hRe(z) ^ 2 + hIm(z) ^ 2)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcnj hcomplex_mult hcomplex_of_hypreal hRe hIm hypreal_add hypreal_mult complex_mult_cnj numeral_2_eq_2)
done


(*---------------------------------------------------------------------------*)
(*  More theorems about hcmod                                                *)
(*---------------------------------------------------------------------------*)

lemma hcomplex_hcmod_eq_zero_cancel: "(hcmod x = 0) = (x = 0)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_zero_def hypreal_zero_num)
done
declare hcomplex_hcmod_eq_zero_cancel [simp]

lemma hcmod_hcomplex_of_hypreal_of_nat:
     "hcmod (hcomplex_of_hypreal(hypreal_of_nat n)) = hypreal_of_nat n"
apply auto
done
declare hcmod_hcomplex_of_hypreal_of_nat [simp]

lemma hcmod_hcomplex_of_hypreal_of_hypnat:
     "hcmod (hcomplex_of_hypreal(hypreal_of_hypnat n)) = hypreal_of_hypnat n"
apply auto
done
declare hcmod_hcomplex_of_hypreal_of_hypnat [simp]

lemma hcmod_minus: "hcmod (-x) = hcmod(x)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_minus)
done
declare hcmod_minus [simp]

lemma hcmod_mult_hcnj: "hcmod(z * hcnj(z)) = hcmod(z) ^ 2"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_mult hcnj hypreal_mult complex_mod_mult_cnj numeral_2_eq_2)
done

lemma hcmod_ge_zero: "(0::hypreal) <= hcmod x"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hypreal_zero_num hypreal_le)
done
declare hcmod_ge_zero [simp]

lemma hrabs_hcmod_cancel: "abs(hcmod x) = hcmod x"
apply (auto intro: hrabs_eqI1)
done
declare hrabs_hcmod_cancel [simp]

lemma hcmod_mult: "hcmod(x*y) = hcmod(x) * hcmod(y)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_mult hypreal_mult complex_mod_mult)
done

lemma hcmod_add_squared_eq:
     "hcmod(x + y) ^ 2 = hcmod(x) ^ 2 + hcmod(y) ^ 2 + 2 * hRe(x * hcnj y)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_add hypreal_mult hRe hcnj hcomplex_mult
                      numeral_2_eq_2 realpow_two [symmetric] 
                 simp del: realpow_Suc)
apply (auto simp add: numeral_2_eq_2 [symmetric] complex_mod_add_squared_eq
                 hypreal_add [symmetric] hypreal_mult [symmetric] 
                 hypreal_of_real_def [symmetric])
done

lemma hcomplex_hRe_mult_hcnj_le_hcmod: "hRe(x * hcnj y) <= hcmod(x * hcnj y)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcnj hcomplex_mult hRe hypreal_le)
done
declare hcomplex_hRe_mult_hcnj_le_hcmod [simp]

lemma hcomplex_hRe_mult_hcnj_le_hcmod2: "hRe(x * hcnj y) <= hcmod(x * y)"
apply (cut_tac x = "x" and y = "y" in hcomplex_hRe_mult_hcnj_le_hcmod)
apply (simp add: hcmod_mult)
done
declare hcomplex_hRe_mult_hcnj_le_hcmod2 [simp]

lemma hcmod_triangle_squared: "hcmod (x + y) ^ 2 <= (hcmod(x) + hcmod(y)) ^ 2"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcnj hcomplex_add hypreal_mult hypreal_add
                      hypreal_le realpow_two [symmetric] numeral_2_eq_2
            simp del: realpow_Suc)
apply (simp (no_asm) add: numeral_2_eq_2 [symmetric])
done
declare hcmod_triangle_squared [simp]

lemma hcmod_triangle_ineq: "hcmod (x + y) <= hcmod(x) + hcmod(y)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_add hypreal_add hypreal_le)
done
declare hcmod_triangle_ineq [simp]

lemma hcmod_triangle_ineq2: "hcmod(b + a) - hcmod b <= hcmod a"
apply (cut_tac x1 = "b" and y1 = "a" and c = "-hcmod b" in hcmod_triangle_ineq [THEN add_right_mono])
apply (simp add: add_ac)
done
declare hcmod_triangle_ineq2 [simp]

lemma hcmod_diff_commute: "hcmod (x - y) = hcmod (y - x)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_diff complex_mod_diff_commute)
done

lemma hcmod_add_less:
     "[| hcmod x < r; hcmod y < s |] ==> hcmod (x + y) < r + s"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (rule_tac z = "r" in eq_Abs_hypreal)
apply (rule_tac z = "s" in eq_Abs_hypreal)
apply (auto simp add: hcmod hcomplex_add hypreal_add hypreal_less)
apply ultra
apply (auto intro: complex_mod_add_less)
done

lemma hcmod_mult_less:
     "[| hcmod x < r; hcmod y < s |] ==> hcmod (x * y) < r * s"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "y" in eq_Abs_hcomplex)
apply (rule_tac z = "r" in eq_Abs_hypreal)
apply (rule_tac z = "s" in eq_Abs_hypreal)
apply (auto simp add: hcmod hypreal_mult hypreal_less hcomplex_mult)
apply ultra
apply (auto intro: complex_mod_mult_less)
done

lemma hcmod_diff_ineq: "hcmod(a) - hcmod(b) <= hcmod(a + b)"
apply (rule_tac z = "a" in eq_Abs_hcomplex)
apply (rule_tac z = "b" in eq_Abs_hcomplex)
apply (auto simp add: hcmod hcomplex_add hypreal_diff hypreal_le)
done
declare hcmod_diff_ineq [simp]



subsection{*A Few Nonlinear Theorems*}

lemma hcpow:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) hcpow
   Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hcomplex(hcomplexrel``{%n. X n ^ Y n})"
apply (unfold hcpow_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma hcomplex_of_hypreal_hyperpow:
     "hcomplex_of_hypreal (x pow n) = (hcomplex_of_hypreal x) hcpow n"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcomplex_of_hypreal hyperpow hcpow complex_of_real_pow)
done

lemma hcmod_hcomplexpow: "hcmod(x ^ n) = hcmod(x) ^ n"
apply (induct_tac "n")
apply (auto simp add: hcmod_mult)
done

lemma hcmod_hcpow: "hcmod(x hcpow n) = hcmod(x) pow n"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcpow hyperpow hcmod complex_mod_complexpow)
done

lemma hcomplexpow_minus:
     "(-x::hcomplex) ^ n = (if even n then (x ^ n) else -(x ^ n))"
apply (induct_tac "n")
apply auto
done

lemma hcpow_minus:
     "(-x::hcomplex) hcpow n =
      (if ( *pNat* even) n then (x hcpow n) else -(x hcpow n))"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcpow hyperpow starPNat hcomplex_minus)
apply ultra
apply (auto simp add: complexpow_minus) 
apply ultra
done

lemma hccomplex_inverse_minus: "inverse(-x) = - inverse (x::hcomplex)"
apply (rule_tac z = "x" in eq_Abs_hcomplex)
apply (auto simp add: hcomplex_inverse hcomplex_minus complex_inverse_minus)
done

lemma hcomplex_div_one: "x / (1::hcomplex) = x"
apply (unfold hcomplex_divide_def)
apply (simp (no_asm))
done
declare hcomplex_div_one [simp]

lemma hcmod_hcomplex_inverse: "hcmod(inverse x) = inverse(hcmod x)"
apply (case_tac "x = 0", simp add: HCOMPLEX_INVERSE_ZERO)
apply (rule_tac c1 = "hcmod x" in hypreal_mult_left_cancel [THEN iffD1])
apply (auto simp add: hcmod_mult [symmetric])
done

lemma hcmod_divide:
      "hcmod(x/y) = hcmod(x)/(hcmod y)"
apply (unfold hcomplex_divide_def hypreal_divide_def)
apply (auto simp add: hcmod_mult hcmod_hcomplex_inverse)
done

lemma hcomplex_inverse_divide:
      "inverse(x/y) = y/(x::hcomplex)"
apply (unfold hcomplex_divide_def)
apply (auto simp add: inverse_mult_distrib hcomplex_mult_commute)
done
declare hcomplex_inverse_divide [simp]

lemma hcomplexpow_mult: "((r::hcomplex) * s) ^ n = (r ^ n) * (s ^ n)"
apply (induct_tac "n")
apply (auto simp add: mult_ac)
done

lemma hcpow_mult: "((r::hcomplex) * s) hcpow n = (r hcpow n) * (s hcpow n)"
apply (rule_tac z = "r" in eq_Abs_hcomplex)
apply (rule_tac z = "s" in eq_Abs_hcomplex)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcpow hypreal_mult hcomplex_mult complexpow_mult)
done

lemma hcomplexpow_zero: "(0::hcomplex) ^ (Suc n) = 0"
apply auto
done
declare hcomplexpow_zero [simp]

lemma hcpow_zero:
   "0 hcpow (n + 1) = 0"
apply (unfold hcomplex_zero_def hypnat_one_def)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcpow hypnat_add)
done
declare hcpow_zero [simp]

lemma hcpow_zero2:
   "0 hcpow (hSuc n) = 0"
apply (unfold hSuc_def)
apply (simp (no_asm))
done
declare hcpow_zero2 [simp]

lemma hcomplexpow_not_zero [rule_format (no_asm)]:
     "r ~= (0::hcomplex) --> r ^ n ~= 0"
apply (induct_tac "n")
apply (auto)
done
declare hcomplexpow_not_zero [simp]
declare hcomplexpow_not_zero [intro]

lemma hcpow_not_zero: "r ~= 0 ==> r hcpow n ~= (0::hcomplex)"
apply (rule_tac z = "r" in eq_Abs_hcomplex)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcpow hcomplex_zero_def)
apply ultra
apply (auto dest: complexpow_zero_zero)
done
declare hcpow_not_zero [simp]
declare hcpow_not_zero [intro]

lemma hcomplexpow_zero_zero: "r ^ n = (0::hcomplex) ==> r = 0"
apply (blast intro: ccontr dest: hcomplexpow_not_zero)
done

lemma hcpow_zero_zero: "r hcpow n = (0::hcomplex) ==> r = 0"
apply (blast intro: ccontr dest: hcpow_not_zero)
done

lemma hcomplex_i_mult_eq: "iii * iii = - 1"
apply (unfold iii_def)
apply (auto simp add: hcomplex_mult hcomplex_one_def hcomplex_minus)
done
declare hcomplex_i_mult_eq [simp]

lemma hcomplexpow_i_squared: "iii ^ 2 = - 1"
apply (simp (no_asm) add: numeral_2_eq_2)
done
declare hcomplexpow_i_squared [simp]

lemma hcomplex_i_not_zero: "iii ~= 0"
apply (unfold iii_def hcomplex_zero_def)
apply auto
done
declare hcomplex_i_not_zero [simp]

lemma hcomplex_mult_eq_zero_cancel1: "x * y ~= (0::hcomplex) ==> x ~= 0"
apply auto
done

lemma hcomplex_mult_eq_zero_cancel2: "x * y ~= (0::hcomplex) ==> y ~= 0"
apply auto
done

lemma hcomplex_mult_not_eq_zero_iff:
     "(x * y ~= (0::hcomplex)) = (x ~= 0 & y ~= 0)"
apply auto
done
declare hcomplex_mult_not_eq_zero_iff [iff]

lemma hcomplex_divide:
  "Abs_hcomplex(hcomplexrel``{%n. X n}) / Abs_hcomplex(hcomplexrel``{%n. Y n}) =
   Abs_hcomplex(hcomplexrel``{%n. X n / Y n})"
apply (unfold hcomplex_divide_def complex_divide_def)
apply (auto simp add: hcomplex_inverse hcomplex_mult)
done


subsection{*The Function @{term hsgn}*}

lemma hsgn:
  "hsgn (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. sgn (X n)})"
apply (unfold hsgn_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply (auto, ultra)
done

lemma hsgn_zero: "hsgn 0 = 0"
apply (unfold hcomplex_zero_def)
apply (simp (no_asm) add: hsgn)
done
declare hsgn_zero [simp]


lemma hsgn_one: "hsgn 1 = 1"
apply (unfold hcomplex_one_def)
apply (simp (no_asm) add: hsgn)
done
declare hsgn_one [simp]

lemma hsgn_minus: "hsgn (-z) = - hsgn(z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hsgn hcomplex_minus sgn_minus)
done

lemma hsgn_eq: "hsgn z = z / hcomplex_of_hypreal (hcmod z)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hsgn hcomplex_divide hcomplex_of_hypreal hcmod sgn_eq)
done

lemma lemma_hypreal_P_EX2:
     "(EX (x::hypreal) y. P x y) =
      (EX f g. P (Abs_hypreal(hyprel `` {f})) (Abs_hypreal(hyprel `` {g})))"
apply auto
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply auto
done

lemma complex_split2:
     "ALL (n::nat). EX x y. (z n) = complex_of_real(x) + ii * complex_of_real(y)"
apply (blast intro: complex_split)
done

(* Interesting proof! *)
lemma hcomplex_split:
     "EX x y. z = hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: lemma_hypreal_P_EX2 hcomplex_of_hypreal iii_def hcomplex_add hcomplex_mult)
apply (cut_tac z = "x" in complex_split2)
apply (drule choice, safe)+
apply (rule_tac x = "f" in exI)
apply (rule_tac x = "fa" in exI)
apply auto
done

lemma hRe_hcomplex_i:
     "hRe(hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)) = x"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hRe iii_def hcomplex_add hcomplex_mult hcomplex_of_hypreal)
done
declare hRe_hcomplex_i [simp]

lemma hIm_hcomplex_i:
     "hIm(hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)) = y"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hIm iii_def hcomplex_add hcomplex_mult hcomplex_of_hypreal)
done
declare hIm_hcomplex_i [simp]

lemma hcmod_i:
     "hcmod (hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)) =
      ( *f* sqrt) (x ^ 2 + y ^ 2)"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal iii_def hcomplex_add hcomplex_mult starfun hypreal_mult hypreal_add hcmod cmod_i numeral_2_eq_2)
done

lemma hcomplex_eq_hRe_eq:
     "hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya =
      hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb
       ==> xa = xb"
apply (unfold iii_def)
apply (rule_tac z = "xa" in eq_Abs_hypreal)
apply (rule_tac z = "ya" in eq_Abs_hypreal)
apply (rule_tac z = "xb" in eq_Abs_hypreal)
apply (rule_tac z = "yb" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_mult hcomplex_add hcomplex_of_hypreal)
apply (ultra)
done

lemma hcomplex_eq_hIm_eq:
     "hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya =
      hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb
       ==> ya = yb"
apply (unfold iii_def)
apply (rule_tac z = "xa" in eq_Abs_hypreal)
apply (rule_tac z = "ya" in eq_Abs_hypreal)
apply (rule_tac z = "xb" in eq_Abs_hypreal)
apply (rule_tac z = "yb" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_mult hcomplex_add hcomplex_of_hypreal)
apply (ultra)
done

lemma hcomplex_eq_cancel_iff:
     "(hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya =
       hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb) =
      ((xa = xb) & (ya = yb))"
apply (auto intro: hcomplex_eq_hIm_eq hcomplex_eq_hRe_eq)
done
declare hcomplex_eq_cancel_iff [simp]

lemma hcomplex_eq_cancel_iffA:
     "(hcomplex_of_hypreal xa + hcomplex_of_hypreal ya * iii =
       hcomplex_of_hypreal xb + hcomplex_of_hypreal yb * iii ) = ((xa = xb) & (ya = yb))"
apply (auto simp add: hcomplex_mult_commute)
done
declare hcomplex_eq_cancel_iffA [iff]

lemma hcomplex_eq_cancel_iffB:
     "(hcomplex_of_hypreal xa + hcomplex_of_hypreal ya * iii =
       hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb) = ((xa = xb) & (ya = yb))"
apply (auto simp add: hcomplex_mult_commute)
done
declare hcomplex_eq_cancel_iffB [iff]

lemma hcomplex_eq_cancel_iffC:
     "(hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya  =
       hcomplex_of_hypreal xb + hcomplex_of_hypreal yb * iii) = ((xa = xb) & (ya = yb))"
apply (auto simp add: hcomplex_mult_commute)
done
declare hcomplex_eq_cancel_iffC [iff]

lemma hcomplex_eq_cancel_iff2:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y =
      hcomplex_of_hypreal xa) = (x = xa & y = 0)"
apply (cut_tac xa = "x" and ya = "y" and xb = "xa" and yb = "0" in hcomplex_eq_cancel_iff)
apply (simp del: hcomplex_eq_cancel_iff)
done
declare hcomplex_eq_cancel_iff2 [simp]

lemma hcomplex_eq_cancel_iff2a:
     "(hcomplex_of_hypreal x + hcomplex_of_hypreal y * iii =
      hcomplex_of_hypreal xa) = (x = xa & y = 0)"
apply (auto simp add: hcomplex_mult_commute)
done
declare hcomplex_eq_cancel_iff2a [simp]

lemma hcomplex_eq_cancel_iff3:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y =
      iii * hcomplex_of_hypreal ya) = (x = 0 & y = ya)"
apply (cut_tac xa = "x" and ya = "y" and xb = "0" and yb = "ya" in hcomplex_eq_cancel_iff)
apply (simp del: hcomplex_eq_cancel_iff)
done
declare hcomplex_eq_cancel_iff3 [simp]

lemma hcomplex_eq_cancel_iff3a:
     "(hcomplex_of_hypreal x + hcomplex_of_hypreal y * iii =
      iii * hcomplex_of_hypreal ya) = (x = 0 & y = ya)"
apply (auto simp add: hcomplex_mult_commute)
done
declare hcomplex_eq_cancel_iff3a [simp]

lemma hcomplex_split_hRe_zero:
     "hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y = 0
      ==> x = 0"
apply (unfold iii_def)
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcomplex_add hcomplex_mult hcomplex_zero_def hypreal_zero_num)
apply ultra
apply (auto simp add: complex_split_Re_zero)
done

lemma hcomplex_split_hIm_zero:
     "hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y = 0
      ==> y = 0"
apply (unfold iii_def)
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcomplex_add hcomplex_mult hcomplex_zero_def hypreal_zero_num)
apply ultra
apply (auto simp add: complex_split_Im_zero)
done

lemma hRe_hsgn: "hRe(hsgn z) = hRe(z)/hcmod z"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hsgn hcmod hRe hypreal_divide)
done
declare hRe_hsgn [simp]

lemma hIm_hsgn: "hIm(hsgn z) = hIm(z)/hcmod z"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: hsgn hcmod hIm hypreal_divide)
done
declare hIm_hsgn [simp]

lemma real_two_squares_add_zero_iff:
     "(x*x + y*y = 0) = ((x::real) = 0 & y = 0)"
apply (auto intro: real_sum_squares_cancel)
done
declare real_two_squares_add_zero_iff [simp]

lemma hcomplex_inverse_complex_split:
     "inverse(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y) =
      hcomplex_of_hypreal(x/(x ^ 2 + y ^ 2)) -
      iii * hcomplex_of_hypreal(y/(x ^ 2 + y ^ 2))"
apply (rule_tac z = "x" in eq_Abs_hypreal)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcomplex_mult hcomplex_add iii_def starfun hypreal_mult hypreal_add hcomplex_inverse hypreal_divide hcomplex_diff complex_inverse_complex_split numeral_2_eq_2)
done

lemma hRe_mult_i_eq:
    "hRe (iii * hcomplex_of_hypreal y) = 0"
apply (unfold iii_def)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcomplex_mult hRe hypreal_zero_num)
done
declare hRe_mult_i_eq [simp]

lemma hIm_mult_i_eq:
    "hIm (iii * hcomplex_of_hypreal y) = y"
apply (unfold iii_def)
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcomplex_mult hIm hypreal_zero_num)
done
declare hIm_mult_i_eq [simp]

lemma hcmod_mult_i: "hcmod (iii * hcomplex_of_hypreal y) = abs y"
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hcmod hypreal_hrabs iii_def hcomplex_mult)
done
declare hcmod_mult_i [simp]

lemma hcmod_mult_i2: "hcmod (hcomplex_of_hypreal y * iii) = abs y"
apply (auto simp add: hcomplex_mult_commute)
done
declare hcmod_mult_i2 [simp]

(*---------------------------------------------------------------------------*)
(*  harg                                                                     *)
(*---------------------------------------------------------------------------*)

lemma harg:
  "harg (Abs_hcomplex(hcomplexrel `` {%n. X n})) =
      Abs_hypreal(hyprel `` {%n. arg (X n)})"

apply (unfold harg_def)
apply (rule_tac f = "Abs_hypreal" in arg_cong)
apply (auto, ultra)
done

lemma cos_harg_i_mult_zero:
     "0 < y ==> ( *f* cos) (harg(iii * hcomplex_of_hypreal y)) = 0"
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal iii_def hcomplex_mult hypreal_zero_num hypreal_less starfun harg)
apply (ultra)
done
declare cos_harg_i_mult_zero [simp]

lemma cos_harg_i_mult_zero2:
     "y < 0 ==> ( *f* cos) (harg(iii * hcomplex_of_hypreal y)) = 0"
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal iii_def hcomplex_mult hypreal_zero_num hypreal_less starfun harg)
apply (ultra)
done
declare cos_harg_i_mult_zero2 [simp]

lemma hcomplex_of_hypreal_not_zero_iff:
     "(hcomplex_of_hypreal y ~= 0) = (y ~= 0)"
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hypreal_zero_num hcomplex_zero_def)
done
declare hcomplex_of_hypreal_not_zero_iff [simp]

lemma hcomplex_of_hypreal_zero_iff: "(hcomplex_of_hypreal y = 0) = (y = 0)"
apply (rule_tac z = "y" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_of_hypreal hypreal_zero_num hcomplex_zero_def)
done
declare hcomplex_of_hypreal_zero_iff [simp]

lemma cos_harg_i_mult_zero3:
     "y ~= 0 ==> ( *f* cos) (harg(iii * hcomplex_of_hypreal y)) = 0"
apply (cut_tac x = "y" and y = "0" in hypreal_linear)
apply auto
done
declare cos_harg_i_mult_zero3 [simp]

(*---------------------------------------------------------------------------*)
(* Polar form for nonstandard complex numbers                                 *)
(*---------------------------------------------------------------------------*)

lemma complex_split_polar2:
     "ALL n. EX r a. (z n) = complex_of_real r *
      (complex_of_real(cos a) + ii * complex_of_real(sin a))"
apply (blast intro: complex_split_polar)
done

lemma hcomplex_split_polar:
  "EX r a. z = hcomplex_of_hypreal r *
   (hcomplex_of_hypreal(( *f* cos) a) + iii * hcomplex_of_hypreal(( *f* sin) a))"
apply (rule_tac z = "z" in eq_Abs_hcomplex)
apply (auto simp add: lemma_hypreal_P_EX2 hcomplex_of_hypreal iii_def starfun hcomplex_add hcomplex_mult)
apply (cut_tac z = "x" in complex_split_polar2)
apply (drule choice, safe)+
apply (rule_tac x = "f" in exI)
apply (rule_tac x = "fa" in exI)
apply auto
done

lemma hcis:
  "hcis (Abs_hypreal(hyprel `` {%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. cis (X n)})"
apply (unfold hcis_def)
apply (rule_tac f = "Abs_hcomplex" in arg_cong)
apply auto
apply (ultra)
done

lemma hcis_eq:
   "hcis a =
    (hcomplex_of_hypreal(( *f* cos) a) +
    iii * hcomplex_of_hypreal(( *f* sin) a))"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: starfun hcis hcomplex_of_hypreal iii_def hcomplex_mult hcomplex_add cis_def)
done

lemma hrcis:
  "hrcis (Abs_hypreal(hyprel `` {%n. X n})) (Abs_hypreal(hyprel `` {%n. Y n})) =
      Abs_hcomplex(hcomplexrel `` {%n. rcis (X n) (Y n)})"
apply (unfold hrcis_def)
apply (auto simp add: hcomplex_of_hypreal hcomplex_mult hcis rcis_def)
done

lemma hrcis_Ex: "EX r a. z = hrcis r a"
apply (simp (no_asm) add: hrcis_def hcis_eq)
apply (rule hcomplex_split_polar)
done

lemma hRe_hcomplex_polar:
     "hRe(hcomplex_of_hypreal r *
      (hcomplex_of_hypreal(( *f* cos) a) +
       iii * hcomplex_of_hypreal(( *f* sin) a))) = r * ( *f* cos) a"
apply (auto simp add: right_distrib hcomplex_of_hypreal_mult mult_ac)
done
declare hRe_hcomplex_polar [simp]

lemma hRe_hrcis: "hRe(hrcis r a) = r * ( *f* cos) a"
apply (unfold hrcis_def)
apply (auto simp add: hcis_eq)
done
declare hRe_hrcis [simp]

lemma hIm_hcomplex_polar:
     "hIm(hcomplex_of_hypreal r *
      (hcomplex_of_hypreal(( *f* cos) a) +
       iii * hcomplex_of_hypreal(( *f* sin) a))) = r * ( *f* sin) a"
apply (auto simp add: right_distrib hcomplex_of_hypreal_mult mult_ac)
done
declare hIm_hcomplex_polar [simp]

lemma hIm_hrcis: "hIm(hrcis r a) = r * ( *f* sin) a"
apply (unfold hrcis_def)
apply (auto simp add: hcis_eq)
done
declare hIm_hrcis [simp]

lemma hcmod_complex_polar:
     "hcmod (hcomplex_of_hypreal r *
      (hcomplex_of_hypreal(( *f* cos) a) +
       iii * hcomplex_of_hypreal(( *f* sin) a))) = abs r"
apply (rule_tac z = "r" in eq_Abs_hypreal)
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: iii_def starfun hcomplex_of_hypreal hcomplex_mult hcmod hcomplex_add hypreal_hrabs)
done
declare hcmod_complex_polar [simp]

lemma hcmod_hrcis: "hcmod(hrcis r a) = abs r"
apply (unfold hrcis_def)
apply (auto simp add: hcis_eq)
done
declare hcmod_hrcis [simp]

(*---------------------------------------------------------------------------*)
(*  (r1 * hrcis a) * (r2 * hrcis b) = r1 * r2 * hrcis (a + b)                *)
(*---------------------------------------------------------------------------*)

lemma hcis_hrcis_eq: "hcis a = hrcis 1 a"
apply (unfold hrcis_def)
apply (simp (no_asm))
done
declare hcis_hrcis_eq [symmetric, simp]

lemma hrcis_mult:
  "hrcis r1 a * hrcis r2 b = hrcis (r1*r2) (a + b)"
apply (unfold hrcis_def)
apply (rule_tac z = "r1" in eq_Abs_hypreal)
apply (rule_tac z = "r2" in eq_Abs_hypreal)
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (rule_tac z = "b" in eq_Abs_hypreal)
apply (auto simp add: hrcis hcis hypreal_add hypreal_mult hcomplex_of_hypreal
                      hcomplex_mult cis_mult [symmetric] 
                      complex_of_real_mult [symmetric])
done

lemma hcis_mult: "hcis a * hcis b = hcis (a + b)"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (rule_tac z = "b" in eq_Abs_hypreal)
apply (auto simp add: hcis hcomplex_mult hypreal_add cis_mult)
done

lemma hcis_zero:
  "hcis 0 = 1"
apply (unfold hcomplex_one_def)
apply (auto simp add: hcis hypreal_zero_num)
done
declare hcis_zero [simp]

lemma hrcis_zero_mod:
  "hrcis 0 a = 0"
apply (unfold hcomplex_zero_def)
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: hrcis hypreal_zero_num)
done
declare hrcis_zero_mod [simp]

lemma hrcis_zero_arg: "hrcis r 0 = hcomplex_of_hypreal r"
apply (rule_tac z = "r" in eq_Abs_hypreal)
apply (auto simp add: hrcis hypreal_zero_num hcomplex_of_hypreal)
done
declare hrcis_zero_arg [simp]

lemma hcomplex_i_mult_minus: "iii * (iii * x) = - x"
apply (simp (no_asm) add: hcomplex_mult_assoc [symmetric])
done
declare hcomplex_i_mult_minus [simp]

lemma hcomplex_i_mult_minus2: "iii * iii * x = - x"
apply (simp (no_asm))
done
declare hcomplex_i_mult_minus2 [simp]

lemma hcis_hypreal_of_nat_Suc_mult:
   "hcis (hypreal_of_nat (Suc n) * a) = hcis a * hcis (hypreal_of_nat n * a)"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: hypreal_of_nat hcis hypreal_mult hcomplex_mult cis_real_of_nat_Suc_mult)
done

lemma NSDeMoivre: "(hcis a) ^ n = hcis (hypreal_of_nat n * a)"
apply (induct_tac "n")
apply (auto simp add: hcis_hypreal_of_nat_Suc_mult)
done

lemma hcis_hypreal_of_hypnat_Suc_mult:
     "hcis (hypreal_of_hypnat (n + 1) * a) =
      hcis a * hcis (hypreal_of_hypnat n * a)"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcis hypreal_of_hypnat hypnat_add hypnat_one_def hypreal_mult hcomplex_mult cis_real_of_nat_Suc_mult)
done

lemma NSDeMoivre_ext: "(hcis a) hcpow n = hcis (hypreal_of_hypnat n * a)"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (rule_tac z = "n" in eq_Abs_hypnat)
apply (auto simp add: hcis hypreal_of_hypnat hypreal_mult hcpow DeMoivre)
done

lemma DeMoivre2:
  "(hrcis r a) ^ n = hrcis (r ^ n) (hypreal_of_nat n * a)"
apply (unfold hrcis_def)
apply (auto simp add: hcomplexpow_mult NSDeMoivre hcomplex_of_hypreal_pow)
done

lemma DeMoivre2_ext:
  "(hrcis r a) hcpow n = hrcis (r pow n) (hypreal_of_hypnat n * a)"
apply (unfold hrcis_def)
apply (auto simp add: hcpow_mult NSDeMoivre_ext hcomplex_of_hypreal_hyperpow)
done

lemma hcis_inverse: "inverse(hcis a) = hcis (-a)"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_inverse hcis hypreal_minus)
done
declare hcis_inverse [simp]

lemma hrcis_inverse: "inverse(hrcis r a) = hrcis (inverse r) (-a)"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (rule_tac z = "r" in eq_Abs_hypreal)
apply (auto simp add: hcomplex_inverse hrcis hypreal_minus hypreal_inverse rcis_inverse)
apply (ultra)
apply (unfold real_divide_def)
apply (auto simp add: INVERSE_ZERO)
done

lemma hRe_hcis: "hRe(hcis a) = ( *f* cos) a"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: hcis starfun hRe)
done
declare hRe_hcis [simp]

lemma hIm_hcis: "hIm(hcis a) = ( *f* sin) a"
apply (rule_tac z = "a" in eq_Abs_hypreal)
apply (auto simp add: hcis starfun hIm)
done
declare hIm_hcis [simp]

lemma cos_n_hRe_hcis_pow_n:
     "( *f* cos) (hypreal_of_nat n * a) = hRe(hcis a ^ n)"
apply (auto simp add: NSDeMoivre)
done

lemma sin_n_hIm_hcis_pow_n:
     "( *f* sin) (hypreal_of_nat n * a) = hIm(hcis a ^ n)"
apply (auto simp add: NSDeMoivre)
done

lemma cos_n_hRe_hcis_hcpow_n:
     "( *f* cos) (hypreal_of_hypnat n * a) = hRe(hcis a hcpow n)"
apply (auto simp add: NSDeMoivre_ext)
done

lemma sin_n_hIm_hcis_hcpow_n:
     "( *f* sin) (hypreal_of_hypnat n * a) = hIm(hcis a hcpow n)"
apply (auto simp add: NSDeMoivre_ext)
done

lemma hexpi_add: "hexpi(a + b) = hexpi(a) * hexpi(b)"
apply (unfold hexpi_def)
apply (rule_tac z = "a" in eq_Abs_hcomplex)
apply (rule_tac z = "b" in eq_Abs_hcomplex)
apply (auto simp add: hcis hRe hIm hcomplex_add hcomplex_mult hypreal_mult starfun hcomplex_of_hypreal cis_mult [symmetric] complex_Im_add complex_Re_add exp_add complex_of_real_mult)
done


subsection{*@{term hcomplex_of_complex} Preserves Field Properties*}

lemma hcomplex_of_complex_add:
     "hcomplex_of_complex (z1 + z2) = hcomplex_of_complex z1 + hcomplex_of_complex z2"
apply (unfold hcomplex_of_complex_def)
apply (simp (no_asm) add: hcomplex_add)
done
declare hcomplex_of_complex_add [simp]

lemma hcomplex_of_complex_mult:
     "hcomplex_of_complex (z1 * z2) = hcomplex_of_complex z1 * hcomplex_of_complex z2"
apply (unfold hcomplex_of_complex_def)
apply (simp (no_asm) add: hcomplex_mult)
done
declare hcomplex_of_complex_mult [simp]

lemma hcomplex_of_complex_eq_iff:
 "(hcomplex_of_complex z1 = hcomplex_of_complex z2) = (z1 = z2)"
apply (unfold hcomplex_of_complex_def)
apply auto
done
declare hcomplex_of_complex_eq_iff [simp]

lemma hcomplex_of_complex_minus:
     "hcomplex_of_complex (-r) = - hcomplex_of_complex  r"
apply (unfold hcomplex_of_complex_def)
apply (auto simp add: hcomplex_minus)
done
declare hcomplex_of_complex_minus [simp]

lemma hcomplex_of_complex_one [simp]:
      "hcomplex_of_complex 1 = 1"
apply (unfold hcomplex_of_complex_def hcomplex_one_def)
apply auto
done

lemma hcomplex_of_complex_zero [simp]:
      "hcomplex_of_complex 0 = 0"
apply (unfold hcomplex_of_complex_def hcomplex_zero_def)
apply (simp (no_asm))
done

lemma hcomplex_of_complex_zero_iff: "(hcomplex_of_complex r = 0) = (r = 0)"
apply (auto intro: FreeUltrafilterNat_P simp add: hcomplex_of_complex_def hcomplex_zero_def)
done

lemma hcomplex_of_complex_inverse:
     "hcomplex_of_complex (inverse r) = inverse (hcomplex_of_complex r)"
apply (case_tac "r=0")
apply (simp add: hcomplex_of_complex_zero)
apply (rule_tac c1 = "hcomplex_of_complex r" 
       in hcomplex_mult_left_cancel [THEN iffD1])
apply (force simp add: hcomplex_of_complex_zero_iff)
apply (subst hcomplex_of_complex_mult [symmetric])
apply (auto simp add: hcomplex_of_complex_one hcomplex_of_complex_zero_iff)
done
declare hcomplex_of_complex_inverse [simp]

lemma hcomplex_of_complex_divide:
     "hcomplex_of_complex (z1 / z2) = hcomplex_of_complex z1 / hcomplex_of_complex z2"
apply (simp (no_asm) add: hcomplex_divide_def complex_divide_def)
done
declare hcomplex_of_complex_divide [simp]

lemma hRe_hcomplex_of_complex:
   "hRe (hcomplex_of_complex z) = hypreal_of_real (Re z)"
apply (unfold hcomplex_of_complex_def hypreal_of_real_def)
apply (auto simp add: hRe)
done

lemma hIm_hcomplex_of_complex:
   "hIm (hcomplex_of_complex z) = hypreal_of_real (Im z)"
apply (unfold hcomplex_of_complex_def hypreal_of_real_def)
apply (auto simp add: hIm)
done

lemma hcmod_hcomplex_of_complex:
     "hcmod (hcomplex_of_complex x) = hypreal_of_real (cmod x)"
apply (unfold hypreal_of_real_def hcomplex_of_complex_def)
apply (auto simp add: hcmod)
done

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
val inj_hcomplex_minus = thm"inj_hcomplex_minus";
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
val HCOMPLEX_INVERSE_ZERO = thm"HCOMPLEX_INVERSE_ZERO";
val HCOMPLEX_DIVISION_BY_ZERO = thm"HCOMPLEX_DIVISION_BY_ZERO";
val hcomplex_mult_inv_left = thm"hcomplex_mult_inv_left";
val hcomplex_mult_left_cancel = thm"hcomplex_mult_left_cancel";
val hcomplex_mult_right_cancel = thm"hcomplex_mult_right_cancel";
val hcomplex_add_divide_distrib = thm"hcomplex_add_divide_distrib";
val hcomplex_of_hypreal = thm"hcomplex_of_hypreal";
val inj_hcomplex_of_hypreal = thm"inj_hcomplex_of_hypreal";
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
val inj_hcnj = thm"inj_hcnj";
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
val hypreal_of_nat_le_iff = thm"hypreal_of_nat_le_iff";
val hypreal_of_nat_ge_zero = thm"hypreal_of_nat_ge_zero";
val hypreal_of_hypnat_ge_zero = thm"hypreal_of_hypnat_ge_zero";
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
val hcomplexpow_minus = thm"hcomplexpow_minus";
val hcpow_minus = thm"hcpow_minus";
val hccomplex_inverse_minus = thm"hccomplex_inverse_minus";
val hcomplex_div_one = thm"hcomplex_div_one";
val hcmod_hcomplex_inverse = thm"hcmod_hcomplex_inverse";
val hcmod_divide = thm"hcmod_divide";
val hcomplex_inverse_divide = thm"hcomplex_inverse_divide";
val hcomplexpow_mult = thm"hcomplexpow_mult";
val hcpow_mult = thm"hcpow_mult";
val hcomplexpow_zero = thm"hcomplexpow_zero";
val hcpow_zero = thm"hcpow_zero";
val hcpow_zero2 = thm"hcpow_zero2";
val hcomplexpow_not_zero = thm"hcomplexpow_not_zero";
val hcpow_not_zero = thm"hcpow_not_zero";
val hcomplexpow_zero_zero = thm"hcomplexpow_zero_zero";
val hcpow_zero_zero = thm"hcpow_zero_zero";
val hcomplex_i_mult_eq = thm"hcomplex_i_mult_eq";
val hcomplexpow_i_squared = thm"hcomplexpow_i_squared";
val hcomplex_i_not_zero = thm"hcomplex_i_not_zero";
val hcomplex_mult_eq_zero_cancel1 = thm"hcomplex_mult_eq_zero_cancel1";
val hcomplex_mult_eq_zero_cancel2 = thm"hcomplex_mult_eq_zero_cancel2";
val hcomplex_mult_not_eq_zero_iff = thm"hcomplex_mult_not_eq_zero_iff";
val hcomplex_divide = thm"hcomplex_divide";
val hsgn = thm"hsgn";
val hsgn_zero = thm"hsgn_zero";
val hsgn_one = thm"hsgn_one";
val hsgn_minus = thm"hsgn_minus";
val hsgn_eq = thm"hsgn_eq";
val lemma_hypreal_P_EX2 = thm"lemma_hypreal_P_EX2";
val complex_split2 = thm"complex_split2";
val hcomplex_split = thm"hcomplex_split";
val hRe_hcomplex_i = thm"hRe_hcomplex_i";
val hIm_hcomplex_i = thm"hIm_hcomplex_i";
val hcmod_i = thm"hcmod_i";
val hcomplex_eq_hRe_eq = thm"hcomplex_eq_hRe_eq";
val hcomplex_eq_hIm_eq = thm"hcomplex_eq_hIm_eq";
val hcomplex_eq_cancel_iff = thm"hcomplex_eq_cancel_iff";
val hcomplex_eq_cancel_iffA = thm"hcomplex_eq_cancel_iffA";
val hcomplex_eq_cancel_iffB = thm"hcomplex_eq_cancel_iffB";
val hcomplex_eq_cancel_iffC = thm"hcomplex_eq_cancel_iffC";
val hcomplex_eq_cancel_iff2 = thm"hcomplex_eq_cancel_iff2";
val hcomplex_eq_cancel_iff2a = thm"hcomplex_eq_cancel_iff2a";
val hcomplex_eq_cancel_iff3 = thm"hcomplex_eq_cancel_iff3";
val hcomplex_eq_cancel_iff3a = thm"hcomplex_eq_cancel_iff3a";
val hcomplex_split_hRe_zero = thm"hcomplex_split_hRe_zero";
val hcomplex_split_hIm_zero = thm"hcomplex_split_hIm_zero";
val hRe_hsgn = thm"hRe_hsgn";
val hIm_hsgn = thm"hIm_hsgn";
val real_two_squares_add_zero_iff = thm"real_two_squares_add_zero_iff";
val hcomplex_inverse_complex_split = thm"hcomplex_inverse_complex_split";
val hRe_mult_i_eq = thm"hRe_mult_i_eq";
val hIm_mult_i_eq = thm"hIm_mult_i_eq";
val hcmod_mult_i = thm"hcmod_mult_i";
val hcmod_mult_i2 = thm"hcmod_mult_i2";
val harg = thm"harg";
val cos_harg_i_mult_zero = thm"cos_harg_i_mult_zero";
val cos_harg_i_mult_zero2 = thm"cos_harg_i_mult_zero2";
val hcomplex_of_hypreal_not_zero_iff = thm"hcomplex_of_hypreal_not_zero_iff";
val hcomplex_of_hypreal_zero_iff = thm"hcomplex_of_hypreal_zero_iff";
val cos_harg_i_mult_zero3 = thm"cos_harg_i_mult_zero3";
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
val hypreal_of_nat = thm"hypreal_of_nat";
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

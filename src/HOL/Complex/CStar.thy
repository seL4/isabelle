(*  Title       : CStar.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
*)

header{*Star-transforms in NSA, Extending Sets of Complex Numbers
      and Complex Functions*}

theory CStar = NSCA:

constdefs

    (* nonstandard extension of sets *)
    starsetC :: "complex set => hcomplex set"          ("*sc* _" [80] 80)
    "*sc* A  == {x. \<forall>X \<in> Rep_hcomplex(x). {n. X n \<in> A} \<in> FreeUltrafilterNat}"

    (* internal sets *)
    starsetC_n :: "(nat => complex set) => hcomplex set"  ("*scn* _" [80] 80)
    "*scn* As  == {x. \<forall>X \<in> Rep_hcomplex(x). 
                      {n. X n \<in> (As n)} \<in> FreeUltrafilterNat}"

    InternalCSets :: "hcomplex set set"
    "InternalCSets == {X. \<exists>As. X = *scn* As}"

    (* star transform of functions f: Complex --> Complex *)

    starfunC :: "(complex => complex) => hcomplex => hcomplex"
                ("*fc* _" [80] 80)
    "*fc* f  == 
        (%x. Abs_hcomplex(\<Union>X \<in> Rep_hcomplex(x). hcomplexrel``{%n. f (X n)}))"

    starfunC_n :: "(nat => (complex => complex)) => hcomplex => hcomplex"
                  ("*fcn* _" [80] 80)
    "*fcn* F  == 
      (%x. Abs_hcomplex(\<Union>X \<in> Rep_hcomplex(x). hcomplexrel``{%n. (F n)(X n)}))"

    InternalCFuns :: "(hcomplex => hcomplex) set"
    "InternalCFuns == {X. \<exists>F. X = *fcn* F}"


    (* star transform of functions f: Real --> Complex *)

    starfunRC :: "(real => complex) => hypreal => hcomplex"
                 ("*fRc* _" [80] 80)
    "*fRc* f  == (%x. Abs_hcomplex(\<Union>X \<in> Rep_hypreal(x). hcomplexrel``{%n. f (X n)}))"

    starfunRC_n :: "(nat => (real => complex)) => hypreal => hcomplex"
                   ("*fRcn* _" [80] 80)
    "*fRcn* F  == (%x. Abs_hcomplex(\<Union>X \<in> Rep_hypreal(x). hcomplexrel``{%n. (F n)(X n)}))"

    InternalRCFuns :: "(hypreal => hcomplex) set"
    "InternalRCFuns == {X. \<exists>F. X = *fRcn* F}"

    (* star transform of functions f: Complex --> Real; needed for Re and Im parts *)

    starfunCR :: "(complex => real) => hcomplex => hypreal"
                 ("*fcR* _" [80] 80)
    "*fcR* f  == (%x. Abs_hypreal(\<Union>X \<in> Rep_hcomplex(x). hyprel``{%n. f (X n)}))"

    starfunCR_n :: "(nat => (complex => real)) => hcomplex => hypreal"
                   ("*fcRn* _" [80] 80)
    "*fcRn* F  == (%x. Abs_hypreal(\<Union>X \<in> Rep_hcomplex(x). hyprel``{%n. (F n)(X n)}))"

    InternalCRFuns :: "(hcomplex => hypreal) set"
    "InternalCRFuns == {X. \<exists>F. X = *fcRn* F}"


subsection{*Properties of the *-Transform Applied to Sets of Reals*}

lemma STARC_complex_set [simp]: "*sc*(UNIV::complex set) = (UNIV)"
by (simp add: starsetC_def)
declare STARC_complex_set

lemma STARC_empty_set: "*sc* {} = {}"
by (simp add: starsetC_def)
declare STARC_empty_set [simp]

lemma STARC_Un: "*sc* (A Un B) = *sc* A Un *sc* B"
apply (auto simp add: starsetC_def)
apply (drule bspec, assumption)
apply (rule_tac z = x in eq_Abs_hcomplex, simp, ultra)
apply (blast intro: FreeUltrafilterNat_subset)+
done

lemma starsetC_n_Un: "*scn* (%n. (A n) Un (B n)) = *scn* A Un *scn* B"
apply (auto simp add: starsetC_n_def)
apply (drule_tac x = Xa in bspec)
apply (rule_tac [2] z = x in eq_Abs_hcomplex)
apply (auto dest!: bspec, ultra+)
done

lemma InternalCSets_Un:
     "[| X \<in> InternalCSets; Y \<in> InternalCSets |] ==> (X Un Y) \<in> InternalCSets"
by (auto simp add:  InternalCSets_def starsetC_n_Un [symmetric])

lemma STARC_Int: "*sc* (A Int B) = *sc* A Int *sc* B"
apply (auto simp add: starsetC_def)
prefer 3 apply (blast intro: FreeUltrafilterNat_Int FreeUltrafilterNat_subset)
apply (blast intro: FreeUltrafilterNat_subset)+
done

lemma starsetC_n_Int: "*scn* (%n. (A n) Int (B n)) = *scn* A Int *scn* B"
apply (auto simp add: starsetC_n_def)
apply (auto dest!: bspec, ultra+)
done

lemma InternalCSets_Int:
    "[| X \<in> InternalCSets; Y \<in> InternalCSets |] ==> (X Int Y) \<in> InternalCSets"
by (auto simp add: InternalCSets_def starsetC_n_Int [symmetric])

lemma STARC_Compl: "*sc* -A = -( *sc* A)"
apply (auto simp add: starsetC_def)
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (rule_tac [2] z = x in eq_Abs_hcomplex)
apply (auto dest!: bspec, ultra+)
done

lemma starsetC_n_Compl: "*scn* ((%n. - A n)) = -( *scn* A)"
apply (auto simp add: starsetC_n_def)
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (rule_tac [2] z = x in eq_Abs_hcomplex)
apply (auto dest!: bspec, ultra+)
done

lemma InternalCSets_Compl: "X :InternalCSets ==> -X \<in> InternalCSets"
by (auto simp add: InternalCSets_def starsetC_n_Compl [symmetric])

lemma STARC_mem_Compl: "x \<notin> *sc* F ==> x \<in> *sc* (- F)"
by (simp add: STARC_Compl)

lemma STARC_diff: "*sc* (A - B) = *sc* A - *sc* B"
by (simp add: Diff_eq STARC_Int STARC_Compl)

lemma starsetC_n_diff:
      "*scn* (%n. (A n) - (B n)) = *scn* A - *scn* B"
apply (auto simp add: starsetC_n_def)
apply (rule_tac [2] z = x in eq_Abs_hcomplex)
apply (rule_tac [3] z = x in eq_Abs_hcomplex)
apply (auto dest!: bspec, ultra+)
done

lemma InternalCSets_diff:
     "[| X \<in> InternalCSets; Y \<in> InternalCSets |] ==> (X - Y) \<in> InternalCSets"
by (auto simp add: InternalCSets_def starsetC_n_diff [symmetric])

lemma STARC_subset: "A \<le> B ==> *sc* A \<le> *sc* B"
apply (simp add: starsetC_def)
apply (blast intro: FreeUltrafilterNat_subset)+
done

lemma STARC_mem: "a \<in> A ==> hcomplex_of_complex a \<in> *sc* A"
apply (simp add: starsetC_def hcomplex_of_complex_def)
apply (auto intro: FreeUltrafilterNat_subset)
done

lemma STARC_hcomplex_of_complex_image_subset:
    "hcomplex_of_complex ` A \<le> *sc* A"
apply (auto simp add: starsetC_def hcomplex_of_complex_def)
apply (blast intro: FreeUltrafilterNat_subset)
done

lemma STARC_SComplex_subset: "SComplex \<le> *sc* (UNIV:: complex set)"
by auto

lemma STARC_hcomplex_of_complex_Int:
     "*sc* X Int SComplex = hcomplex_of_complex ` X"
apply (auto simp add: starsetC_def hcomplex_of_complex_def SComplex_def)
apply (fold hcomplex_of_complex_def)
apply (rule imageI, rule ccontr)
apply (drule bspec)
apply (rule lemma_hcomplexrel_refl)
prefer 2 apply (blast intro: FreeUltrafilterNat_subset, auto)
done

lemma lemma_not_hcomplexA:
     "x \<notin> hcomplex_of_complex ` A ==> \<forall>y \<in> A. x \<noteq> hcomplex_of_complex y"
by auto

lemma starsetC_starsetC_n_eq: "*sc* X = *scn* (%n. X)"
by (simp add: starsetC_n_def starsetC_def)

lemma InternalCSets_starsetC_n [simp]: "( *sc* X) \<in> InternalCSets"
by (auto simp add: InternalCSets_def starsetC_starsetC_n_eq)

lemma InternalCSets_UNIV_diff:
    "X \<in> InternalCSets ==> UNIV - X \<in> InternalCSets"
by (auto intro: InternalCSets_Compl)

text{*Nonstandard extension of a set (defined using a constant sequence) as a special case of an internal set*}

lemma starsetC_n_starsetC: "\<forall>n. (As n = A) ==> *scn* As = *sc* A"
by (simp add:starsetC_n_def starsetC_def)


subsection{*Theorems about Nonstandard Extensions of Functions*}

lemma starfunC_n_starfunC: "\<forall>n. (F n = f) ==> *fcn* F = *fc* f"
by (simp add: starfunC_n_def starfunC_def)

lemma starfunRC_n_starfunRC: "\<forall>n. (F n = f) ==> *fRcn* F = *fRc* f"
by (simp add: starfunRC_n_def starfunRC_def)

lemma starfunCR_n_starfunCR: "\<forall>n. (F n = f) ==> *fcRn* F = *fcR* f"
by (simp add: starfunCR_n_def starfunCR_def)

lemma starfunC_congruent:
      "congruent hcomplexrel (%X. hcomplexrel``{%n. f (X n)})"
apply (auto simp add: hcomplexrel_iff congruent_def, ultra)
done

(* f::complex => complex *)
lemma starfunC:
      "( *fc* f) (Abs_hcomplex(hcomplexrel``{%n. X n})) =
       Abs_hcomplex(hcomplexrel `` {%n. f (X n)})"
apply (simp add: starfunC_def)
apply (rule arg_cong [where f = Abs_hcomplex])
apply (auto iff add: hcomplexrel_iff, ultra)
done

lemma starfunRC:
      "( *fRc* f) (Abs_hypreal(hyprel``{%n. X n})) =
       Abs_hcomplex(hcomplexrel `` {%n. f (X n)})"
apply (simp add: starfunRC_def)
apply (rule arg_cong [where f = Abs_hcomplex], auto, ultra)
done

lemma starfunCR:
      "( *fcR* f) (Abs_hcomplex(hcomplexrel``{%n. X n})) =
       Abs_hypreal(hyprel `` {%n. f (X n)})"
apply (simp add: starfunCR_def)
apply (rule arg_cong [where f = Abs_hypreal])
apply (auto iff add: hcomplexrel_iff, ultra)
done

(**  multiplication: ( *f) x ( *g) = *(f x g) **)

lemma starfunC_mult: "( *fc* f) z * ( *fc* g) z = ( *fc* (%x. f x * g x)) z"
apply (rule_tac z = z in eq_Abs_hcomplex)
apply (auto simp add: starfunC hcomplex_mult)
done
declare starfunC_mult [symmetric, simp]

lemma starfunRC_mult:
    "( *fRc* f) z * ( *fRc* g) z = ( *fRc* (%x. f x * g x)) z"
apply (rule eq_Abs_hypreal [of z])
apply (simp add: starfunRC hcomplex_mult)
done
declare starfunRC_mult [symmetric, simp]

lemma starfunCR_mult:
    "( *fcR* f) z * ( *fcR* g) z = ( *fcR* (%x. f x * g x)) z"
apply (rule_tac z = z in eq_Abs_hcomplex)
apply (simp add: starfunCR hypreal_mult)
done
declare starfunCR_mult [symmetric, simp]

(**  addition: ( *f) + ( *g) = *(f + g)  **)

lemma starfunC_add: "( *fc* f) z + ( *fc* g) z = ( *fc* (%x. f x + g x)) z"
apply (rule_tac z = z in eq_Abs_hcomplex)
apply (simp add: starfunC hcomplex_add)
done
declare starfunC_add [symmetric, simp]

lemma starfunRC_add: "( *fRc* f) z + ( *fRc* g) z = ( *fRc* (%x. f x + g x)) z"
apply (rule eq_Abs_hypreal [of z])
apply (simp add: starfunRC hcomplex_add)
done
declare starfunRC_add [symmetric, simp]

lemma starfunCR_add: "( *fcR* f) z + ( *fcR* g) z = ( *fcR* (%x. f x + g x)) z"
apply (rule_tac z = z in eq_Abs_hcomplex)
apply (simp add: starfunCR hypreal_add)
done
declare starfunCR_add [symmetric, simp]

(**  uminus **)
lemma starfunC_minus [simp]: "( *fc* (%x. - f x)) x = - ( *fc* f) x"
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (simp add: starfunC hcomplex_minus)
done

lemma starfunRC_minus [simp]: "( *fRc* (%x. - f x)) x = - ( *fRc* f) x"
apply (rule eq_Abs_hypreal [of x])
apply (simp add: starfunRC hcomplex_minus)
done

lemma starfunCR_minus [simp]: "( *fcR* (%x. - f x)) x = - ( *fcR* f) x"
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (simp add: starfunCR hypreal_minus)
done

(**  addition: ( *f) - ( *g) = *(f - g)  **)

lemma starfunC_diff: "( *fc* f) y  - ( *fc* g) y = ( *fc* (%x. f x - g x)) y"
by (simp add: diff_minus)
declare starfunC_diff [symmetric, simp]

lemma starfunRC_diff:
    "( *fRc* f) y  - ( *fRc* g) y = ( *fRc* (%x. f x - g x)) y"
by (simp add: diff_minus)
declare starfunRC_diff [symmetric, simp]

lemma starfunCR_diff:
  "( *fcR* f) y  - ( *fcR* g) y = ( *fcR* (%x. f x - g x)) y"
by (simp add: diff_minus)
declare starfunCR_diff [symmetric, simp]

(**  composition: ( *f) o ( *g) = *(f o g) **)

lemma starfunC_o2: "(%x. ( *fc* f) (( *fc* g) x)) = *fc* (%x. f (g x))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (simp add: starfunC)
done

lemma starfunC_o: "( *fc* f) o ( *fc* g) = ( *fc* (f o g))"
by (simp add: o_def starfunC_o2)

lemma starfunC_starfunRC_o2:
    "(%x. ( *fc* f) (( *fRc* g) x)) = *fRc* (%x. f (g x))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (simp add: starfunRC starfunC)
done

lemma starfun_starfunCR_o2:
    "(%x. ( *f* f) (( *fcR* g) x)) = *fcR* (%x. f (g x))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (simp add: starfunCR starfun)
done

lemma starfunC_starfunRC_o: "( *fc* f) o ( *fRc* g) = ( *fRc* (f o g))"
by (simp add: o_def starfunC_starfunRC_o2)

lemma starfun_starfunCR_o: "( *f* f) o ( *fcR* g) = ( *fcR* (f o g))"
by (simp add: o_def starfun_starfunCR_o2)

lemma starfunC_const_fun [simp]: "( *fc* (%x. k)) z = hcomplex_of_complex k"
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunC hcomplex_of_complex_def)
done

lemma starfunRC_const_fun [simp]: "( *fRc* (%x. k)) z = hcomplex_of_complex k"
apply (rule eq_Abs_hypreal [of z])
apply (simp add: starfunRC hcomplex_of_complex_def)
done

lemma starfunCR_const_fun [simp]: "( *fcR* (%x. k)) z = hypreal_of_real k"
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunCR hypreal_of_real_def)
done

lemma starfunC_inverse: "inverse (( *fc* f) x) = ( *fc* (%x. inverse (f x))) x"
apply (rule eq_Abs_hcomplex [of x])
apply (simp add: starfunC hcomplex_inverse)
done
declare starfunC_inverse [symmetric, simp]

lemma starfunRC_inverse:
    "inverse (( *fRc* f) x) = ( *fRc* (%x. inverse (f x))) x"
apply (rule eq_Abs_hypreal [of x])
apply (simp add: starfunRC hcomplex_inverse)
done
declare starfunRC_inverse [symmetric, simp]

lemma starfunCR_inverse:
    "inverse (( *fcR* f) x) = ( *fcR* (%x. inverse (f x))) x"
apply (rule eq_Abs_hcomplex [of x])
apply (simp add: starfunCR hypreal_inverse)
done
declare starfunCR_inverse [symmetric, simp]

lemma starfunC_eq [simp]:
    "( *fc* f) (hcomplex_of_complex a) = hcomplex_of_complex (f a)"
by (simp add: starfunC hcomplex_of_complex_def)

lemma starfunRC_eq [simp]:
    "( *fRc* f) (hypreal_of_real a) = hcomplex_of_complex (f a)"
by (simp add: starfunRC hcomplex_of_complex_def hypreal_of_real_def)

lemma starfunCR_eq [simp]:
    "( *fcR* f) (hcomplex_of_complex a) = hypreal_of_real (f a)"
by (simp add: starfunCR hcomplex_of_complex_def hypreal_of_real_def)

lemma starfunC_capprox:
    "( *fc* f) (hcomplex_of_complex a) @c= hcomplex_of_complex (f a)"
by auto

lemma starfunRC_capprox:
    "( *fRc* f) (hypreal_of_real a) @c= hcomplex_of_complex (f a)"
by auto

lemma starfunCR_approx:
    "( *fcR* f) (hcomplex_of_complex a) @= hypreal_of_real (f a)"
by auto

(*
Goal "( *fcNat* (%n. z ^ n)) N = (hcomplex_of_complex z) hcpow N"
*)

lemma starfunC_hcpow: "( *fc* (%z. z ^ n)) Z = Z hcpow hypnat_of_nat n"
apply (rule eq_Abs_hcomplex [of Z])
apply (simp add: hcpow starfunC hypnat_of_nat_eq)
done

lemma starfunC_lambda_cancel:
    "( *fc* (%h. f (x + h))) y  = ( *fc* f) (hcomplex_of_complex  x + y)"
apply (rule eq_Abs_hcomplex [of y])
apply (simp add: starfunC hcomplex_of_complex_def hcomplex_add)
done

lemma starfunCR_lambda_cancel:
    "( *fcR* (%h. f (x + h))) y  = ( *fcR* f) (hcomplex_of_complex  x + y)"
apply (rule eq_Abs_hcomplex [of y])
apply (simp add: starfunCR hcomplex_of_complex_def hcomplex_add)
done

lemma starfunRC_lambda_cancel:
    "( *fRc* (%h. f (x + h))) y  = ( *fRc* f) (hypreal_of_real x + y)"
apply (rule eq_Abs_hypreal [of y])
apply (simp add: starfunRC hypreal_of_real_def hypreal_add)
done

lemma starfunC_lambda_cancel2:
    "( *fc* (%h. f(g(x + h)))) y = ( *fc* (f o g)) (hcomplex_of_complex x + y)"
apply (rule eq_Abs_hcomplex [of y])
apply (simp add: starfunC hcomplex_of_complex_def hcomplex_add)
done

lemma starfunCR_lambda_cancel2:
    "( *fcR* (%h. f(g(x + h)))) y = ( *fcR* (f o g)) (hcomplex_of_complex x + y)"
apply (rule eq_Abs_hcomplex [of y])
apply (simp add: starfunCR hcomplex_of_complex_def hcomplex_add)
done

lemma starfunRC_lambda_cancel2:
    "( *fRc* (%h. f(g(x + h)))) y = ( *fRc* (f o g)) (hypreal_of_real x + y)"
apply (rule eq_Abs_hypreal [of y])
apply (simp add: starfunRC hypreal_of_real_def hypreal_add)
done

lemma starfunC_mult_CFinite_capprox:
    "[| ( *fc* f) y @c= l; ( *fc* g) y @c= m; l: CFinite; m: CFinite |]
     ==>  ( *fc* (%x. f x * g x)) y @c= l * m"
apply (drule capprox_mult_CFinite, assumption+)
apply (auto intro: capprox_sym [THEN [2] capprox_CFinite])
done

lemma starfunCR_mult_HFinite_capprox:
    "[| ( *fcR* f) y @= l; ( *fcR* g) y @= m; l: HFinite; m: HFinite |]
     ==>  ( *fcR* (%x. f x * g x)) y @= l * m"
apply (drule approx_mult_HFinite, assumption+)
apply (auto intro: approx_sym [THEN [2] approx_HFinite])
done

lemma starfunRC_mult_CFinite_capprox:
    "[| ( *fRc* f) y @c= l; ( *fRc* g) y @c= m; l: CFinite; m: CFinite |]
     ==>  ( *fRc* (%x. f x * g x)) y @c= l * m"
apply (drule capprox_mult_CFinite, assumption+)
apply (auto intro: capprox_sym [THEN [2] capprox_CFinite])
done

lemma starfunC_add_capprox:
    "[| ( *fc* f) y @c= l; ( *fc* g) y @c= m |]
     ==>  ( *fc* (%x. f x + g x)) y @c= l + m"
by (auto intro: capprox_add)

lemma starfunRC_add_capprox:
    "[| ( *fRc* f) y @c= l; ( *fRc* g) y @c= m |]
     ==>  ( *fRc* (%x. f x + g x)) y @c= l + m"
by (auto intro: capprox_add)

lemma starfunCR_add_approx:
    "[| ( *fcR* f) y @= l; ( *fcR* g) y @= m
               |] ==>  ( *fcR* (%x. f x + g x)) y @= l + m"
by (auto intro: approx_add)

lemma starfunCR_cmod: "*fcR* cmod = hcmod"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hcomplex)
apply (simp add: starfunCR hcmod)
done

lemma starfunC_inverse_inverse: "( *fc* inverse) x = inverse(x)"
apply (rule eq_Abs_hcomplex [of x])
apply (simp add: starfunC hcomplex_inverse)
done

lemma starfunC_divide: "( *fc* f) y  / ( *fc* g) y = ( *fc* (%x. f x / g x)) y"
by (simp add: divide_inverse)
declare starfunC_divide [symmetric, simp]

lemma starfunCR_divide:
  "( *fcR* f) y  / ( *fcR* g) y = ( *fcR* (%x. f x / g x)) y"
by (simp add: divide_inverse)
declare starfunCR_divide [symmetric, simp]

lemma starfunRC_divide:
  "( *fRc* f) y  / ( *fRc* g) y = ( *fRc* (%x. f x / g x)) y"
by (simp add: divide_inverse)
declare starfunRC_divide [symmetric, simp]


subsection{*Internal Functions - Some Redundancy With *Fc* Now*}

lemma starfunC_n_congruent:
      "congruent hcomplexrel (%X. hcomplexrel``{%n. f n (X n)})"
by (auto simp add: congruent_def hcomplexrel_iff, ultra)

lemma starfunC_n:
     "( *fcn* f) (Abs_hcomplex(hcomplexrel``{%n. X n})) =
      Abs_hcomplex(hcomplexrel `` {%n. f n (X n)})"
apply (simp add: starfunC_n_def)
apply (rule arg_cong [where f = Abs_hcomplex])
apply (auto iff add: hcomplexrel_iff, ultra)
done

(**  multiplication: ( *fn) x ( *gn) = *(fn x gn) **)

lemma starfunC_n_mult:
    "( *fcn* f) z * ( *fcn* g) z = ( *fcn* (% i x. f i x * g i x)) z"
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunC_n hcomplex_mult)
done

(**  addition: ( *fn) + ( *gn) = *(fn + gn) **)

lemma starfunC_n_add:
    "( *fcn* f) z + ( *fcn* g) z = ( *fcn* (%i x. f i x + g i x)) z"
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunC_n hcomplex_add)
done

(** uminus **)

lemma starfunC_n_minus: "- ( *fcn* g) z = ( *fcn* (%i x. - g i x)) z"
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunC_n hcomplex_minus)
done

(** subtraction: ( *fn) - ( *gn) = *(fn - gn) **)

lemma starfunNat_n_diff:
   "( *fcn* f) z - ( *fcn* g) z = ( *fcn* (%i x. f i x - g i x)) z"
by (simp add: diff_minus  starfunC_n_add starfunC_n_minus)

(** composition: ( *fn) o ( *gn) = *(fn o gn) **)

lemma starfunC_n_const_fun [simp]:
     "( *fcn* (%i x. k)) z = hcomplex_of_complex  k"
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunC_n hcomplex_of_complex_def)
done

lemma starfunC_n_eq [simp]:
    "( *fcn* f) (hcomplex_of_complex n) = Abs_hcomplex(hcomplexrel `` {%i. f i n})"
by (simp add: starfunC_n hcomplex_of_complex_def)

lemma starfunC_eq_iff: "(( *fc* f) = ( *fc* g)) = (f = g)"
apply auto
apply (rule ext, rule ccontr)
apply (drule_tac x = "hcomplex_of_complex (x) " in fun_cong)
apply (simp add: starfunC hcomplex_of_complex_def)
done

lemma starfunRC_eq_iff: "(( *fRc* f) = ( *fRc* g)) = (f = g)"
apply auto
apply (rule ext, rule ccontr)
apply (drule_tac x = "hypreal_of_real (x) " in fun_cong)
apply auto
done

lemma starfunCR_eq_iff: "(( *fcR* f) = ( *fcR* g)) = (f = g)"
apply auto
apply (rule ext, rule ccontr)
apply (drule_tac x = "hcomplex_of_complex (x) " in fun_cong)
apply auto
done

lemma starfunC_eq_Re_Im_iff:
    "(( *fc* f) x = z) = ((( *fcR* (%x. Re(f x))) x = hRe (z)) &
                          (( *fcR* (%x. Im(f x))) x = hIm (z)))"
apply (rule eq_Abs_hcomplex [of x])
apply (rule eq_Abs_hcomplex [of z])
apply (auto simp add: starfunCR starfunC hIm hRe complex_Re_Im_cancel_iff, ultra+)
done

lemma starfunC_approx_Re_Im_iff:
    "(( *fc* f) x @c= z) = ((( *fcR* (%x. Re(f x))) x @= hRe (z)) &
                            (( *fcR* (%x. Im(f x))) x @= hIm (z)))"
apply (rule eq_Abs_hcomplex [of x])
apply (rule eq_Abs_hcomplex [of z])
apply (simp add: starfunCR starfunC hIm hRe capprox_approx_iff)
done

lemma starfunC_Idfun_capprox:
    "x @c= hcomplex_of_complex a ==> ( *fc* (%x. x)) x @c= hcomplex_of_complex  a"
apply (rule eq_Abs_hcomplex [of x])
apply (simp add: starfunC)
done

lemma starfunC_Id [simp]: "( *fc* (%x. x)) x = x"
apply (rule eq_Abs_hcomplex [of x])
apply (simp add: starfunC)
done

ML
{*
val STARC_complex_set = thm "STARC_complex_set";
val STARC_empty_set = thm "STARC_empty_set";
val STARC_Un = thm "STARC_Un";
val starsetC_n_Un = thm "starsetC_n_Un";
val InternalCSets_Un = thm "InternalCSets_Un";
val STARC_Int = thm "STARC_Int";
val starsetC_n_Int = thm "starsetC_n_Int";
val InternalCSets_Int = thm "InternalCSets_Int";
val STARC_Compl = thm "STARC_Compl";
val starsetC_n_Compl = thm "starsetC_n_Compl";
val InternalCSets_Compl = thm "InternalCSets_Compl";
val STARC_mem_Compl = thm "STARC_mem_Compl";
val STARC_diff = thm "STARC_diff";
val starsetC_n_diff = thm "starsetC_n_diff";
val InternalCSets_diff = thm "InternalCSets_diff";
val STARC_subset = thm "STARC_subset";
val STARC_mem = thm "STARC_mem";
val STARC_hcomplex_of_complex_image_subset = thm "STARC_hcomplex_of_complex_image_subset";
val STARC_SComplex_subset = thm "STARC_SComplex_subset";
val STARC_hcomplex_of_complex_Int = thm "STARC_hcomplex_of_complex_Int";
val lemma_not_hcomplexA = thm "lemma_not_hcomplexA";
val starsetC_starsetC_n_eq = thm "starsetC_starsetC_n_eq";
val InternalCSets_starsetC_n = thm "InternalCSets_starsetC_n";
val InternalCSets_UNIV_diff = thm "InternalCSets_UNIV_diff";
val starsetC_n_starsetC = thm "starsetC_n_starsetC";
val starfunC_n_starfunC = thm "starfunC_n_starfunC";
val starfunRC_n_starfunRC = thm "starfunRC_n_starfunRC";
val starfunCR_n_starfunCR = thm "starfunCR_n_starfunCR";
val starfunC_congruent = thm "starfunC_congruent";
val starfunC = thm "starfunC";
val starfunRC = thm "starfunRC";
val starfunCR = thm "starfunCR";
val starfunC_mult = thm "starfunC_mult";
val starfunRC_mult = thm "starfunRC_mult";
val starfunCR_mult = thm "starfunCR_mult";
val starfunC_add = thm "starfunC_add";
val starfunRC_add = thm "starfunRC_add";
val starfunCR_add = thm "starfunCR_add";
val starfunC_minus = thm "starfunC_minus";
val starfunRC_minus = thm "starfunRC_minus";
val starfunCR_minus = thm "starfunCR_minus";
val starfunC_diff = thm "starfunC_diff";
val starfunRC_diff = thm "starfunRC_diff";
val starfunCR_diff = thm "starfunCR_diff";
val starfunC_o2 = thm "starfunC_o2";
val starfunC_o = thm "starfunC_o";
val starfunC_starfunRC_o2 = thm "starfunC_starfunRC_o2";
val starfun_starfunCR_o2 = thm "starfun_starfunCR_o2";
val starfunC_starfunRC_o = thm "starfunC_starfunRC_o";
val starfun_starfunCR_o = thm "starfun_starfunCR_o";
val starfunC_const_fun = thm "starfunC_const_fun";
val starfunRC_const_fun = thm "starfunRC_const_fun";
val starfunCR_const_fun = thm "starfunCR_const_fun";
val starfunC_inverse = thm "starfunC_inverse";
val starfunRC_inverse = thm "starfunRC_inverse";
val starfunCR_inverse = thm "starfunCR_inverse";
val starfunC_eq = thm "starfunC_eq";
val starfunRC_eq = thm "starfunRC_eq";
val starfunCR_eq = thm "starfunCR_eq";
val starfunC_capprox = thm "starfunC_capprox";
val starfunRC_capprox = thm "starfunRC_capprox";
val starfunCR_approx = thm "starfunCR_approx";
val starfunC_hcpow = thm "starfunC_hcpow";
val starfunC_lambda_cancel = thm "starfunC_lambda_cancel";
val starfunCR_lambda_cancel = thm "starfunCR_lambda_cancel";
val starfunRC_lambda_cancel = thm "starfunRC_lambda_cancel";
val starfunC_lambda_cancel2 = thm "starfunC_lambda_cancel2";
val starfunCR_lambda_cancel2 = thm "starfunCR_lambda_cancel2";
val starfunRC_lambda_cancel2 = thm "starfunRC_lambda_cancel2";
val starfunC_mult_CFinite_capprox = thm "starfunC_mult_CFinite_capprox";
val starfunCR_mult_HFinite_capprox = thm "starfunCR_mult_HFinite_capprox";
val starfunRC_mult_CFinite_capprox = thm "starfunRC_mult_CFinite_capprox";
val starfunC_add_capprox = thm "starfunC_add_capprox";
val starfunRC_add_capprox = thm "starfunRC_add_capprox";
val starfunCR_add_approx = thm "starfunCR_add_approx";
val starfunCR_cmod = thm "starfunCR_cmod";
val starfunC_inverse_inverse = thm "starfunC_inverse_inverse";
val starfunC_divide = thm "starfunC_divide";
val starfunCR_divide = thm "starfunCR_divide";
val starfunRC_divide = thm "starfunRC_divide";
val starfunC_n_congruent = thm "starfunC_n_congruent";
val starfunC_n = thm "starfunC_n";
val starfunC_n_mult = thm "starfunC_n_mult";
val starfunC_n_add = thm "starfunC_n_add";
val starfunC_n_minus = thm "starfunC_n_minus";
val starfunNat_n_diff = thm "starfunNat_n_diff";
val starfunC_n_const_fun = thm "starfunC_n_const_fun";
val starfunC_n_eq = thm "starfunC_n_eq";
val starfunC_eq_iff = thm "starfunC_eq_iff";
val starfunRC_eq_iff = thm "starfunRC_eq_iff";
val starfunCR_eq_iff = thm "starfunCR_eq_iff";
val starfunC_eq_Re_Im_iff = thm "starfunC_eq_Re_Im_iff";
val starfunC_approx_Re_Im_iff = thm "starfunC_approx_Re_Im_iff";
val starfunC_Idfun_capprox = thm "starfunC_Idfun_capprox";
val starfunC_Id = thm "starfunC_Id";
*}

end

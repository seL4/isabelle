(*  Title       : CLim.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Limits, Continuity and Differentiation for Complex Functions*}

theory CLim
imports CSeries
begin

(*not in simpset?*)
declare hypreal_epsilon_not_zero [simp]

(*??generalize*)
lemma lemma_complex_mult_inverse_squared [simp]:
     "x \<noteq> (0::complex) \<Longrightarrow> (x * inverse(x) ^ 2) = inverse x"
by (simp add: numeral_2_eq_2)

text{*Changing the quantified variable. Install earlier?*}
lemma all_shift: "(\<forall>x::'a::comm_ring_1. P x) = (\<forall>x. P (x-a))";
apply auto 
apply (drule_tac x="x+a" in spec) 
apply (simp add: diff_minus add_assoc) 
done

lemma complex_add_minus_iff [simp]: "(x + - a = (0::complex)) = (x=a)"
by (simp add: diff_eq_eq diff_minus [symmetric])

lemma complex_add_eq_0_iff [iff]: "(x+y = (0::complex)) = (y = -x)"
apply auto
apply (drule sym [THEN diff_eq_eq [THEN iffD2]], auto)
done

abbreviation
  CLIM :: "[complex=>complex,complex,complex] => bool"
				("((_)/ -- (_)/ --C> (_))" [60, 0, 60] 60) where
  "CLIM == LIM"

abbreviation
  NSCLIM :: "[complex=>complex,complex,complex] => bool"
			      ("((_)/ -- (_)/ --NSC> (_))" [60, 0, 60] 60) where
  "NSCLIM == NSLIM"

abbreviation
  (* f: C --> R *)
  CRLIM :: "[complex=>real,complex,real] => bool"
				("((_)/ -- (_)/ --CR> (_))" [60, 0, 60] 60) where
  "CRLIM == LIM"

abbreviation
  NSCRLIM :: "[complex=>real,complex,real] => bool"
			      ("((_)/ -- (_)/ --NSCR> (_))" [60, 0, 60] 60) where
  "NSCRLIM == NSLIM"

abbreviation
  isContc :: "[complex=>complex,complex] => bool" where
  "isContc == isCont"

abbreviation
  (* NS definition dispenses with limit notions *)
  isNSContc :: "[complex=>complex,complex] => bool" where
  "isNSContc == isNSCont"

abbreviation
  isContCR :: "[complex=>real,complex] => bool" where
  "isContCR == isCont"

abbreviation
  (* NS definition dispenses with limit notions *)
  isNSContCR :: "[complex=>real,complex] => bool" where
  "isNSContCR == isNSCont"

abbreviation
  isUContc :: "(complex=>complex) => bool" where
  "isUContc == isUCont"

abbreviation
  isNSUContc :: "(complex=>complex) => bool" where
  "isNSUContc == isNSUCont"


lemma CLIM_def:
  "f -- a --C> L =
     (\<forall>r. 0 < r -->
	     (\<exists>s. 0 < s & (\<forall>x. (x \<noteq> a & (cmod(x - a) < s)
			  --> cmod(f x - L) < r))))"
by (rule LIM_def)

lemma NSCLIM_def:
  "f -- a --NSC> L = (\<forall>x. (x \<noteq> hcomplex_of_complex a &
           		         x @= hcomplex_of_complex a
                                   --> ( *f* f) x @= hcomplex_of_complex L))"
by (rule NSLIM_def)

lemma CRLIM_def:
  "f -- a --CR> L =
     (\<forall>r. 0 < r -->
	     (\<exists>s. 0 < s & (\<forall>x. (x \<noteq> a & (cmod(x - a) < s)
			  --> abs(f x - L) < r))))"
by (simp add: LIM_def)

lemma NSCRLIM_def:
  "f -- a --NSCR> L = (\<forall>x. (x \<noteq> hcomplex_of_complex a &
           		         x @= hcomplex_of_complex a
                                   --> ( *f* f) x @= hypreal_of_real L))"
by (rule NSLIM_def)

lemma isContc_def:
  "isContc f a = (f -- a --C> (f a))"
by (rule isCont_def)

lemma isNSContc_def:
  "isNSContc f a = (\<forall>y. y @= hcomplex_of_complex a -->
			   ( *f* f) y @= hcomplex_of_complex (f a))"
by (rule isNSCont_def)

lemma isContCR_def:
  "isContCR f a = (f -- a --CR> (f a))"
by (rule isCont_def)

lemma isNSContCR_def:
  "isNSContCR f a = (\<forall>y. y @= hcomplex_of_complex a -->
			   ( *f* f) y @= hypreal_of_real (f a))"
by (rule isNSCont_def)

lemma isUContc_def:
  "isUContc f =  (\<forall>r. 0 < r -->
		      (\<exists>s. 0 < s & (\<forall>x y. cmod(x - y) < s
			    --> cmod(f x - f y) < r)))"
by (rule isUCont_def)

lemma isNSUContc_def:
  "isNSUContc f = (\<forall>x y. x @= y --> ( *f* f) x @= ( *f* f) y)"
by (rule isNSUCont_def)


  (* differentiation: D is derivative of function f at x *)
definition
  cderiv:: "[complex=>complex,complex,complex] => bool"
			    ("(CDERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60) where
  "CDERIV f x :> D = ((%h. (f(x + h) - f(x))/h) -- 0 --C> D)"

definition
  nscderiv :: "[complex=>complex,complex,complex] => bool"
			    ("(NSCDERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60) where
  "NSCDERIV f x :> D = (\<forall>h \<in> Infinitesimal - {0}.
			      (( *f* f)(hcomplex_of_complex x + h)
        			 - hcomplex_of_complex (f x))/h @= hcomplex_of_complex D)"

definition
  cdifferentiable :: "[complex=>complex,complex] => bool"
                     (infixl "cdifferentiable" 60) where
  "f cdifferentiable x = (\<exists>D. CDERIV f x :> D)"

definition
  NSCdifferentiable :: "[complex=>complex,complex] => bool"
                        (infixl "NSCdifferentiable" 60) where
  "f NSCdifferentiable x = (\<exists>D. NSCDERIV f x :> D)"


subsection{*Limit of Complex to Complex Function*}

lemma NSCLIM_NSCRLIM_Re: "f -- a --NSC> L ==> (%x. Re(f x)) -- a --NSCR> Re(L)"
by (simp add: NSLIM_def starfunC_approx_Re_Im_iff 
              hRe_hcomplex_of_complex)


lemma NSCLIM_NSCRLIM_Im: "f -- a --NSC> L ==> (%x. Im(f x)) -- a --NSCR> Im(L)"
by (simp add: NSLIM_def starfunC_approx_Re_Im_iff 
              hIm_hcomplex_of_complex)

lemma CLIM_NSCLIM:
      "f -- x --C> L ==> f -- x --NSC> L"
by (rule LIM_NSLIM)

lemma eq_Abs_star_ALL: "(\<forall>t. P t) = (\<forall>X. P (star_n X))"
apply auto
apply (rule_tac x = t in star_cases, auto)
done

lemma lemma_CLIM:
     "\<forall>s. 0 < s --> (\<exists>xa.  xa \<noteq> x &
         cmod (xa - x) < s  & r \<le> cmod (f xa - L))
      ==> \<forall>(n::nat). \<exists>xa.  xa \<noteq> x &
              cmod(xa - x) < inverse(real(Suc n)) & r \<le> cmod(f xa - L)"
apply clarify
apply (cut_tac n1 = n in real_of_nat_Suc_gt_zero [THEN positive_imp_inverse_positive], auto)
done


lemma lemma_skolemize_CLIM2:
     "\<forall>s. 0 < s --> (\<exists>xa.  xa \<noteq> x &
         cmod (xa - x) < s  & r \<le> cmod (f xa - L))
      ==> \<exists>X. \<forall>(n::nat). X n \<noteq> x &
                cmod(X n - x) < inverse(real(Suc n)) & r \<le> cmod(f (X n) - L)"
apply (drule lemma_CLIM)
apply (drule choice, blast)
done

lemma lemma_csimp:
     "\<forall>n. X n \<noteq> x &
          cmod (X n - x) < inverse (real(Suc n)) &
          r \<le> cmod (f (X n) - L) ==>
          \<forall>n. cmod (X n - x) < inverse (real(Suc n))"
by auto

lemma NSCLIM_CLIM:
     "f -- x --NSC> L ==> f -- x --C> L"
by (rule NSLIM_LIM)


text{*First key result*}
theorem CLIM_NSCLIM_iff: "(f -- x --C> L) = (f -- x --NSC> L)"
by (rule LIM_NSLIM_iff)


subsection{*Limit of Complex to Real Function*}

lemma CRLIM_NSCRLIM: "f -- x --CR> L ==> f -- x --NSCR> L"
by (rule LIM_NSLIM)

lemma lemma_CRLIM:
     "\<forall>s. 0 < s --> (\<exists>xa.  xa \<noteq> x &
         cmod (xa - x) < s  & r \<le> abs (f xa - L))
      ==> \<forall>(n::nat). \<exists>xa.  xa \<noteq> x &
              cmod(xa - x) < inverse(real(Suc n)) & r \<le> abs (f xa - L)"
apply clarify
apply (cut_tac n1 = n in real_of_nat_Suc_gt_zero [THEN positive_imp_inverse_positive], auto)
done

lemma lemma_skolemize_CRLIM2:
     "\<forall>s. 0 < s --> (\<exists>xa.  xa \<noteq> x &
         cmod (xa - x) < s  & r \<le> abs (f xa - L))
      ==> \<exists>X. \<forall>(n::nat). X n \<noteq> x &
                cmod(X n - x) < inverse(real(Suc n)) & r \<le> abs (f (X n) - L)"
apply (drule lemma_CRLIM)
apply (drule choice, blast)
done

lemma lemma_crsimp:
     "\<forall>n. X n \<noteq> x &
          cmod (X n - x) < inverse (real(Suc n)) &
          r \<le> abs (f (X n) - L) ==>
      \<forall>n. cmod (X n - x) < inverse (real(Suc n))"
by auto

lemma NSCRLIM_CRLIM: "f -- x --NSCR> L ==> f -- x --CR> L"
by (rule NSLIM_LIM)

text{*Second key result*}
theorem CRLIM_NSCRLIM_iff: "(f -- x --CR> L) = (f -- x --NSCR> L)"
by (rule LIM_NSLIM_iff)

(** get this result easily now **)
lemma CLIM_CRLIM_Re: "f -- a --C> L ==> (%x. Re(f x)) -- a --CR> Re(L)"
by (auto dest: NSCLIM_NSCRLIM_Re simp add: CLIM_NSCLIM_iff CRLIM_NSCRLIM_iff [symmetric])

lemma CLIM_CRLIM_Im: "f -- a --C> L ==> (%x. Im(f x)) -- a --CR> Im(L)"
by (auto dest: NSCLIM_NSCRLIM_Im simp add: CLIM_NSCLIM_iff CRLIM_NSCRLIM_iff [symmetric])

lemma CLIM_cnj: "f -- a --C> L ==> (%x. cnj (f x)) -- a --C> cnj L"
by (simp add: CLIM_def complex_cnj_diff [symmetric])

lemma CLIM_cnj_iff: "((%x. cnj (f x)) -- a --C> cnj L) = (f -- a --C> L)"
by (simp add: CLIM_def complex_cnj_diff [symmetric])

(*** NSLIM_add hence CLIM_add *)

lemma NSCLIM_add:
     "[| f -- x --NSC> l; g -- x --NSC> m |]
      ==> (%x. f(x) + g(x)) -- x --NSC> (l + m)"
by (rule NSLIM_add)

lemma CLIM_add:
     "[| f -- x --C> l; g -- x --C> m |]
      ==> (%x. f(x) + g(x)) -- x --C> (l + m)"
by (rule LIM_add)

(*** NSLIM_mult hence CLIM_mult *)

lemma NSCLIM_mult:
     "[| f -- x --NSC> l; g -- x --NSC> m |]
      ==> (%x. f(x) * g(x)) -- x --NSC> (l * m)"
by (rule NSLIM_mult)

lemma CLIM_mult:
     "[| f -- x --C> l; g -- x --C> m |]
      ==> (%x. f(x) * g(x)) -- x --C> (l * m)"
by (rule LIM_mult2)

(*** NSCLIM_const and CLIM_const ***)

lemma NSCLIM_const [simp]: "(%x. k) -- x --NSC> k"
by (rule NSLIM_const)

lemma CLIM_const [simp]: "(%x. k) -- x --C> k"
by (rule LIM_const)

(*** NSCLIM_minus and CLIM_minus ***)

lemma NSCLIM_minus: "f -- a --NSC> L ==> (%x. -f(x)) -- a --NSC> -L"
by (rule NSLIM_minus)

lemma CLIM_minus: "f -- a --C> L ==> (%x. -f(x)) -- a --C> -L"
by (rule LIM_minus)

(*** NSCLIM_diff hence CLIM_diff ***)

lemma NSCLIM_diff:
     "[| f -- x --NSC> l; g -- x --NSC> m |]
      ==> (%x. f(x) - g(x)) -- x --NSC> (l - m)"
by (simp add: diff_minus NSCLIM_add NSCLIM_minus)

lemma CLIM_diff:
     "[| f -- x --C> l; g -- x --C> m |]
      ==> (%x. f(x) - g(x)) -- x --C> (l - m)"
by (rule LIM_diff)

(*** NSCLIM_inverse and hence CLIM_inverse *)

lemma NSCLIM_inverse:
     "[| f -- a --NSC> L;  L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --NSC> (inverse L)"
by (rule NSLIM_inverse)

lemma CLIM_inverse:
     "[| f -- a --C> L;  L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --C> (inverse L)"
by (rule LIM_inverse)

(*** NSCLIM_zero, CLIM_zero, etc. ***)

lemma NSCLIM_zero: "f -- a --NSC> l ==> (%x. f(x) - l) -- a --NSC> 0"
apply (simp add: diff_minus)
apply (rule_tac a1 = l in right_minus [THEN subst])
apply (rule NSCLIM_add, auto) 
done

lemma CLIM_zero: "f -- a --C> l ==> (%x. f(x) - l) -- a --C> 0"
by (simp add: CLIM_NSCLIM_iff NSCLIM_zero)

lemma NSCLIM_zero_cancel: "(%x. f(x) - l) -- x --NSC> 0 ==> f -- x --NSC> l"
by (rule NSLIM_zero_cancel)

lemma CLIM_zero_cancel: "(%x. f(x) - l) -- x --C> 0 ==> f -- x --C> l"
by (rule LIM_zero_cancel)

(*** NSCLIM_not zero and hence CLIM_not_zero ***)

lemma NSCLIM_not_zero: "k \<noteq> 0 ==> ~ ((%x. k) -- x --NSC> 0)"
apply (auto simp del: star_of_zero simp add: NSCLIM_def)
apply (rule_tac x = "hcomplex_of_complex x + hcomplex_of_hypreal epsilon" in exI)
apply (auto intro: Infinitesimal_add_approx_self [THEN approx_sym]
            simp del: star_of_zero)
done

(* [| k \<noteq> 0; (%x. k) -- x --NSC> 0 |] ==> R *)
lemmas NSCLIM_not_zeroE = NSCLIM_not_zero [THEN notE, standard]

lemma CLIM_not_zero: "k \<noteq> 0 ==> ~ ((%x. k) -- x --C> 0)"
by (simp add: CLIM_NSCLIM_iff NSCLIM_not_zero)

(*** NSCLIM_const hence CLIM_const ***)

lemma NSCLIM_const_eq: "(%x. k) -- x --NSC> L ==> k = L"
apply (rule ccontr)
apply (drule NSCLIM_zero)
apply (rule NSCLIM_not_zeroE [of "k-L"], auto)
done

lemma CLIM_const_eq: "(%x. k) -- x --C> L ==> k = L"
by (rule LIM_const_eq)

(*** NSCLIM and hence CLIM are unique ***)

lemma NSCLIM_unique: "[| f -- x --NSC> L; f -- x --NSC> M |] ==> L = M"
apply (drule NSCLIM_minus)
apply (drule NSCLIM_add, assumption)
apply (auto dest!: NSCLIM_const_eq [symmetric])
done

lemma CLIM_unique: "[| f -- x --C> L; f -- x --C> M |] ==> L = M"
by (rule LIM_unique)

(***  NSCLIM_mult_zero and CLIM_mult_zero ***)

lemma NSCLIM_mult_zero:
     "[| f -- x --NSC> 0; g -- x --NSC> 0 |] ==> (%x. f(x)*g(x)) -- x --NSC> 0"
by (rule NSLIM_mult_zero)

lemma CLIM_mult_zero:
     "[| f -- x --C> 0; g -- x --C> 0 |] ==> (%x. f(x)*g(x)) -- x --C> 0"
by (rule LIM_mult_zero)

(*** NSCLIM_self hence CLIM_self ***)

lemma NSCLIM_self: "(%x. x) -- a --NSC> a"
by (rule NSLIM_self)

lemma CLIM_self: "(%x. x) -- a --C> a"
by (rule LIM_self)

(** another equivalence result **)
lemma NSCLIM_NSCRLIM_iff:
   "(f -- x --NSC> L) = ((%y. cmod(f y - L)) -- x --NSCR> 0)"
apply (auto simp add: NSCLIM_def NSCRLIM_def Infinitesimal_approx_minus [symmetric] Infinitesimal_hcmod_iff)
apply (auto dest!: spec) 
apply (rule_tac [!] x = xa in star_cases)
apply (auto simp add: star_n_diff starfun hcmod mem_infmal_iff star_of_def)
done

(** much, much easier standard proof **)
lemma CLIM_CRLIM_iff: "(f -- x --C> L) = ((%y. cmod(f y - L)) -- x --CR> 0)"
by (simp add: CLIM_def CRLIM_def)

(* so this is nicer nonstandard proof *)
lemma NSCLIM_NSCRLIM_iff2:
     "(f -- x --NSC> L) = ((%y. cmod(f y - L)) -- x --NSCR> 0)"
by (simp add: CRLIM_NSCRLIM_iff [symmetric] CLIM_CRLIM_iff CLIM_NSCLIM_iff [symmetric])

lemma NSCLIM_NSCRLIM_Re_Im_iff:
     "(f -- a --NSC> L) = ((%x. Re(f x)) -- a --NSCR> Re(L) &
                            (%x. Im(f x)) -- a --NSCR> Im(L))"
apply (auto intro: NSCLIM_NSCRLIM_Re NSCLIM_NSCRLIM_Im)
apply (auto simp add: NSCLIM_def NSCRLIM_def)
apply (auto dest!: spec) 
apply (rule_tac x = x in star_cases)
apply (simp add: approx_approx_iff starfun star_of_def)
done

lemma CLIM_CRLIM_Re_Im_iff:
     "(f -- a --C> L) = ((%x. Re(f x)) -- a --CR> Re(L) &
                         (%x. Im(f x)) -- a --CR> Im(L))"
by (simp add: CLIM_NSCLIM_iff CRLIM_NSCRLIM_iff NSCLIM_NSCRLIM_Re_Im_iff)


subsection{*Continuity*}

lemma isNSContcD:
      "[| isNSContc f a; y @= hcomplex_of_complex a |]
       ==> ( *f* f) y @= hcomplex_of_complex (f a)"
by (simp add: isNSContc_def)

lemma isNSContc_NSCLIM: "isNSContc f a ==> f -- a --NSC> (f a) "
by (rule isNSCont_NSLIM)

lemma NSCLIM_isNSContc:
      "f -- a --NSC> (f a) ==> isNSContc f a"
by (rule NSLIM_isNSCont)

text{*Nonstandard continuity can be defined using NS Limit in 
similar fashion to standard definition of continuity*}

lemma isNSContc_NSCLIM_iff: "(isNSContc f a) = (f -- a --NSC> (f a))"
by (rule isNSCont_NSLIM_iff)

lemma isNSContc_CLIM_iff: "(isNSContc f a) = (f -- a --C> (f a))"
by (rule isNSCont_LIM_iff)

(*** key result for continuity ***)
lemma isNSContc_isContc_iff: "(isNSContc f a) = (isContc f a)"
by (rule isNSCont_isCont_iff)

lemma isContc_isNSContc: "isContc f a ==> isNSContc f a"
by (rule isCont_isNSCont)

lemma isNSContc_isContc: "isNSContc f a ==> isContc f a"
by (rule isNSCont_isCont)


text{*Alternative definition of continuity*}
lemma NSCLIM_h_iff: "(f -- a --NSC> L) = ((%h. f(a + h)) -- 0 --NSC> L)"
by (rule NSLIM_h_iff)

lemma NSCLIM_isContc_iff:
     "(f -- a --NSC> f a) = ((%h. f(a + h)) -- 0 --NSC> f a)"
by (rule NSCLIM_h_iff)

lemma CLIM_isContc_iff: "(f -- a --C> f a) = ((%h. f(a + h)) -- 0 --C> f(a))"
by (rule LIM_isCont_iff)

lemma isContc_iff: "(isContc f x) = ((%h. f(x + h)) -- 0 --C> f(x))"
by (rule isCont_iff)

lemma isContc_add:
     "[| isContc f a; isContc g a |] ==> isContc (%x. f(x) + g(x)) a"
by (rule isCont_add)

lemma isContc_mult:
     "[| isContc f a; isContc g a |] ==> isContc (%x. f(x) * g(x)) a"
by (rule isCont_mult)


lemma isContc_o: "[| isContc f a; isContc g (f a) |] ==> isContc (g o f) a"
by (rule isCont_o)

lemma isContc_o2:
     "[| isContc f a; isContc g (f a) |] ==> isContc (%x. g (f x)) a"
by (rule isCont_o2)

lemma isNSContc_minus: "isNSContc f a ==> isNSContc (%x. - f x) a"
by (rule isNSCont_minus)

lemma isContc_minus: "isContc f a ==> isContc (%x. - f x) a"
by (rule isCont_minus)

lemma isContc_inverse:
      "[| isContc f x; f x \<noteq> 0 |] ==> isContc (%x. inverse (f x)) x"
by (rule isCont_inverse)

lemma isNSContc_inverse:
     "[| isNSContc f x; f x \<noteq> 0 |] ==> isNSContc (%x. inverse (f x)) x"
by (rule isNSCont_inverse)

lemma isContc_diff:
      "[| isContc f a; isContc g a |] ==> isContc (%x. f(x) - g(x)) a"
by (rule isCont_diff)

lemma isContc_const [simp]: "isContc (%x. k) a"
by (rule isCont_const)

lemma isNSContc_const [simp]: "isNSContc (%x. k) a"
by (rule isNSCont_const)


subsection{*Functions from Complex to Reals*}

lemma isNSContCRD:
      "[| isNSContCR f a; y @= hcomplex_of_complex a |]
       ==> ( *f* f) y @= hypreal_of_real (f a)"
by (simp add: isNSContCR_def)

lemma isNSContCR_NSCRLIM: "isNSContCR f a ==> f -- a --NSCR> (f a) "
by (rule isNSCont_NSLIM)

lemma NSCRLIM_isNSContCR: "f -- a --NSCR> (f a) ==> isNSContCR f a"
by (rule NSLIM_isNSCont)

lemma isNSContCR_NSCRLIM_iff: "(isNSContCR f a) = (f -- a --NSCR> (f a))"
by (rule isNSCont_NSLIM_iff)

lemma isNSContCR_CRLIM_iff: "(isNSContCR f a) = (f -- a --CR> (f a))"
by (rule isNSCont_LIM_iff)

(*** another key result for continuity ***)
lemma isNSContCR_isContCR_iff: "(isNSContCR f a) = (isContCR f a)"
by (rule isNSCont_isCont_iff)

lemma isContCR_isNSContCR: "isContCR f a ==> isNSContCR f a"
by (rule isCont_isNSCont)

lemma isNSContCR_isContCR: "isNSContCR f a ==> isContCR f a"
by (rule isNSCont_isCont)

lemma isNSContCR_cmod [simp]: "isNSContCR cmod (a)"
by (auto intro: approx_hcmod_approx 
         simp add: starfunCR_cmod hcmod_hcomplex_of_complex [symmetric] 
                    isNSContCR_def) 

lemma isContCR_cmod [simp]: "isContCR cmod (a)"
by (simp add: isNSContCR_isContCR_iff [symmetric])

lemma isContc_isContCR_Re: "isContc f a ==> isContCR (%x. Re (f x)) a"
by (simp add: isContc_def isContCR_def CLIM_CRLIM_Re)

lemma isContc_isContCR_Im: "isContc f a ==> isContCR (%x. Im (f x)) a"
by (simp add: isContc_def isContCR_def CLIM_CRLIM_Im)


subsection{*Derivatives*}

lemma CDERIV_iff: "(CDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --C> D)"
by (simp add: cderiv_def)

lemma CDERIV_NSC_iff:
      "(CDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NSC> D)"
by (simp add: cderiv_def CLIM_NSCLIM_iff)

lemma CDERIVD: "CDERIV f x :> D ==> (%h. (f(x + h) - f(x))/h) -- 0 --C> D"
by (simp add: cderiv_def)

lemma NSC_DERIVD: "CDERIV f x :> D ==> (%h. (f(x + h) - f(x))/h) -- 0 --NSC> D"
by (simp add: cderiv_def CLIM_NSCLIM_iff)

text{*Uniqueness*}
lemma CDERIV_unique: "[| CDERIV f x :> D; CDERIV f x :> E |] ==> D = E"
by (simp add: cderiv_def CLIM_unique)

(*** uniqueness: a nonstandard proof ***)
lemma NSCDeriv_unique: "[| NSCDERIV f x :> D; NSCDERIV f x :> E |] ==> D = E"
apply (simp add: nscderiv_def)
apply (auto dest!: bspec [where x = "hcomplex_of_hypreal epsilon"]
            intro!: inj_hcomplex_of_complex [THEN injD] dest: approx_trans3)
done


subsection{* Differentiability*}

lemma CDERIV_CLIM_iff:
     "((%h. (f(a + h) - f(a))/h) -- 0 --C> D) =
      ((%x. (f(x) - f(a)) / (x - a)) -- a --C> D)"
apply (simp add: CLIM_def)
apply (rule_tac f=All in arg_cong) 
apply (rule ext) 
apply (rule imp_cong) 
apply (rule refl) 
apply (rule_tac f=Ex in arg_cong) 
apply (rule ext) 
apply (rule conj_cong) 
apply (rule refl) 
apply (rule trans) 
apply (rule all_shift [where a=a], simp) 
done

lemma CDERIV_iff2:
     "(CDERIV f x :> D) = ((%z. (f(z) - f(x)) / (z - x)) -- x --C> D)"
by (simp add: cderiv_def CDERIV_CLIM_iff)


subsection{* Equivalence of NS and Standard Differentiation*}

(*** first equivalence ***)
lemma NSCDERIV_NSCLIM_iff:
      "(NSCDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NSC> D)"
apply (simp add: nscderiv_def NSCLIM_def, auto)
apply (drule_tac x = xa in bspec)
apply (rule_tac [3] ccontr)
apply (drule_tac [3] x = h in spec)
apply (auto simp add: mem_infmal_iff starfun_lambda_cancel)
done

(*** 2nd equivalence ***)
lemma NSCDERIV_NSCLIM_iff2:
     "(NSCDERIV f x :> D) = ((%z. (f(z) - f(x)) / (z - x)) -- x --NSC> D)"
by (simp add: NSCDERIV_NSCLIM_iff CDERIV_CLIM_iff CLIM_NSCLIM_iff [symmetric])

lemma NSCDERIV_iff2:
     "(NSCDERIV f x :> D) =
      (\<forall>xa. xa \<noteq> hcomplex_of_complex x & xa @= hcomplex_of_complex x -->
        ( *f* (%z. (f z - f x) / (z - x))) xa @= hcomplex_of_complex D)"
by (simp add: NSCDERIV_NSCLIM_iff2 NSCLIM_def)

lemma NSCDERIV_CDERIV_iff: "(NSCDERIV f x :> D) = (CDERIV f x :> D)"
by (simp add: cderiv_def NSCDERIV_NSCLIM_iff CLIM_NSCLIM_iff)

lemma NSCDERIV_isNSContc: "NSCDERIV f x :> D ==> isNSContc f x"
apply (auto simp add: nscderiv_def isNSContc_NSCLIM_iff NSCLIM_def)
apply (drule approx_minus_iff [THEN iffD1])
apply (subgoal_tac "xa - (hcomplex_of_complex x) \<noteq> 0")
 prefer 2 apply (simp add: compare_rls) 
apply (drule_tac x = "xa - hcomplex_of_complex x" in bspec)
apply (simp add: mem_infmal_iff)
apply (simp add: add_assoc [symmetric]) 
apply (auto simp add: mem_infmal_iff [symmetric] add_commute)
apply (drule_tac c = "xa - hcomplex_of_complex x" in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc)
apply (drule_tac x3 = D in 
       HFinite_hcomplex_of_complex [THEN [2] Infinitesimal_HFinite_mult,
                                    THEN mem_infmal_iff [THEN iffD1]])
apply (blast intro: approx_trans mult_commute [THEN subst] approx_minus_iff [THEN iffD2])
done

lemma CDERIV_isContc: "CDERIV f x :> D ==> isContc f x"
by (simp add: NSCDERIV_CDERIV_iff [symmetric] isNSContc_isContc_iff [symmetric] NSCDERIV_isNSContc)

text{* Differentiation rules for combinations of functions follow by clear, 
straightforard algebraic manipulations*}

(* use simple constant nslimit theorem *)
lemma NSCDERIV_const [simp]: "(NSCDERIV (%x. k) x :> 0)"
by (simp add: NSCDERIV_NSCLIM_iff)

lemma CDERIV_const [simp]: "(CDERIV (%x. k) x :> 0)"
by (simp add: NSCDERIV_CDERIV_iff [symmetric])

lemma NSCDERIV_add:
     "[| NSCDERIV f x :> Da;  NSCDERIV g x :> Db |]
      ==> NSCDERIV (%x. f x + g x) x :> Da + Db"
apply (simp add: NSCDERIV_NSCLIM_iff NSCLIM_def, clarify)
apply (auto dest!: spec simp add: add_divide_distrib diff_minus)
apply (drule_tac b = "hcomplex_of_complex Da" and d = "hcomplex_of_complex Db" in approx_add)
apply (auto simp add: add_ac)
done

lemma CDERIV_add:
     "[| CDERIV f x :> Da; CDERIV g x :> Db |]
      ==> CDERIV (%x. f x + g x) x :> Da + Db"
by (simp add: NSCDERIV_add NSCDERIV_CDERIV_iff [symmetric])


subsection{*Lemmas for Multiplication*}

lemma lemma_nscderiv1: "((a::hcomplex)*b) - (c*d) = (b*(a - c)) + (c*(b - d))"
by (simp add: right_diff_distrib)

lemma lemma_nscderiv2:
     "[| (x - y) / z = hcomplex_of_complex D + yb; z \<noteq> 0;
         z : Infinitesimal; yb : Infinitesimal |]
      ==> x - y @= 0"
apply (frule_tac c1 = z in hcomplex_mult_right_cancel [THEN iffD2], assumption)
apply (erule_tac V = " (x - y) / z = hcomplex_of_complex D + yb" in thin_rl)
apply (auto intro!: Infinitesimal_HFinite_mult2 HFinite_add 
            simp add: mem_infmal_iff [symmetric])
apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma NSCDERIV_mult:
     "[| NSCDERIV f x :> Da; NSCDERIV g x :> Db |]
      ==> NSCDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
apply (auto simp add: NSCDERIV_NSCLIM_iff NSCLIM_def)
apply (auto dest!: spec
      simp add: starfun_lambda_cancel lemma_nscderiv1)
apply (simp (no_asm) add: add_divide_distrib diff_divide_distrib)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply (auto simp add: times_divide_eq_right [symmetric]
            simp del: times_divide_eq)
apply (drule_tac D = Db in lemma_nscderiv2, assumption+)
apply (drule_tac
        approx_minus_iff [THEN iffD2, THEN bex_Infinitesimal_iff2 [THEN iffD2]])
apply (auto intro!: approx_add_mono1 simp add: left_distrib right_distrib mult_commute add_assoc)
apply (rule_tac b1 = "hcomplex_of_complex Db * hcomplex_of_complex (f x) " in add_commute [THEN subst])
apply (auto intro!: Infinitesimal_add_approx_self2 [THEN approx_sym] 
		    Infinitesimal_add Infinitesimal_mult
		    Infinitesimal_hcomplex_of_complex_mult
		    Infinitesimal_hcomplex_of_complex_mult2
            simp add: add_assoc [symmetric])
done

lemma CDERIV_mult:
     "[| CDERIV f x :> Da; CDERIV g x :> Db |]
      ==> CDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
by (simp add: NSCDERIV_mult NSCDERIV_CDERIV_iff [symmetric])

lemma NSCDERIV_cmult: "NSCDERIV f x :> D ==> NSCDERIV (%x. c * f x) x :> c*D"
apply (simp add: times_divide_eq_right [symmetric] NSCDERIV_NSCLIM_iff 
                 minus_mult_right right_distrib [symmetric] diff_minus
            del: times_divide_eq_right minus_mult_right [symmetric])
apply (erule NSCLIM_const [THEN NSCLIM_mult])
done

lemma CDERIV_cmult: "CDERIV f x :> D ==> CDERIV (%x. c * f x) x :> c*D"
by (simp add: NSCDERIV_cmult NSCDERIV_CDERIV_iff [symmetric])

lemma NSCDERIV_minus: "NSCDERIV f x :> D ==> NSCDERIV (%x. -(f x)) x :> -D"
apply (simp add: NSCDERIV_NSCLIM_iff diff_minus)
apply (rule_tac t = "f x" in minus_minus [THEN subst])
apply (simp (no_asm_simp) add: minus_add_distrib [symmetric]
            del: minus_add_distrib minus_minus)
apply (erule NSCLIM_minus)
done

lemma CDERIV_minus: "CDERIV f x :> D ==> CDERIV (%x. -(f x)) x :> -D"
by (simp add: NSCDERIV_minus NSCDERIV_CDERIV_iff [symmetric])

lemma NSCDERIV_add_minus:
     "[| NSCDERIV f x :> Da; NSCDERIV g x :> Db |]
      ==> NSCDERIV (%x. f x + -g x) x :> Da + -Db"
by (blast dest: NSCDERIV_add NSCDERIV_minus)

lemma CDERIV_add_minus:
     "[| CDERIV f x :> Da; CDERIV g x :> Db |]
      ==> CDERIV (%x. f x + -g x) x :> Da + -Db"
by (blast dest: CDERIV_add CDERIV_minus)

lemma NSCDERIV_diff:
     "[| NSCDERIV f x :> Da; NSCDERIV g x :> Db |]
      ==> NSCDERIV (%x. f x - g x) x :> Da - Db"
by (simp add: diff_minus NSCDERIV_add_minus)

lemma CDERIV_diff:
     "[| CDERIV f x :> Da; CDERIV g x :> Db |]
       ==> CDERIV (%x. f x - g x) x :> Da - Db"
by (simp add: diff_minus CDERIV_add_minus)


subsection{*Chain Rule*}

(* lemmas *)
lemma NSCDERIV_zero:
      "[| NSCDERIV g x :> D;
          ( *f* g) (hcomplex_of_complex(x) + xa) = hcomplex_of_complex(g x);
          xa : Infinitesimal; xa \<noteq> 0
       |] ==> D = 0"
apply (simp add: nscderiv_def)
apply (drule bspec, auto)
done

lemma NSCDERIV_approx:
  "[| NSCDERIV f x :> D;  h: Infinitesimal;  h \<noteq> 0 |]
   ==> ( *f* f) (hcomplex_of_complex(x) + h) - hcomplex_of_complex(f x) @= 0"
apply (simp add: nscderiv_def mem_infmal_iff [symmetric])
apply (rule Infinitesimal_ratio)
apply (rule_tac [3] approx_hcomplex_of_complex_HFinite, auto)
done


(*--------------------------------------------------*)
(* from one version of differentiability            *)
(*                                                  *)
(*   f(x) - f(a)                                    *)
(* --------------- @= Db                            *)
(*     x - a                                        *)
(* -------------------------------------------------*)

lemma NSCDERIVD1:
   "[| NSCDERIV f (g x) :> Da;
       ( *f* g) (hcomplex_of_complex(x) + xa) \<noteq> hcomplex_of_complex (g x);
       ( *f* g) (hcomplex_of_complex(x) + xa) @= hcomplex_of_complex (g x)|]
    ==> (( *f* f) (( *f* g) (hcomplex_of_complex(x) + xa))
	 - hcomplex_of_complex (f (g x))) /
	(( *f* g) (hcomplex_of_complex(x) + xa) - hcomplex_of_complex (g x))
	   @= hcomplex_of_complex (Da)"
by (simp add: NSCDERIV_NSCLIM_iff2 NSCLIM_def)

(*--------------------------------------------------*)
(* from other version of differentiability          *)
(*                                                  *)
(*  f(x + h) - f(x)                                 *)
(* ----------------- @= Db                          *)
(*         h                                        *)
(*--------------------------------------------------*)

lemma NSCDERIVD2:
  "[| NSCDERIV g x :> Db; xa: Infinitesimal; xa \<noteq> 0 |]
   ==> (( *f* g) (hcomplex_of_complex x + xa) - hcomplex_of_complex(g x)) / xa
       @= hcomplex_of_complex (Db)"
by (simp add: NSCDERIV_NSCLIM_iff NSCLIM_def mem_infmal_iff starfun_lambda_cancel)

lemma lemma_complex_chain: "(z::hcomplex) \<noteq> 0 ==> x*y = (x*inverse(z))*(z*y)"
by auto


text{*Chain rule*}
theorem NSCDERIV_chain:
     "[| NSCDERIV f (g x) :> Da; NSCDERIV g x :> Db |]
      ==> NSCDERIV (f o g) x :> Da * Db"
apply (simp (no_asm_simp) add: NSCDERIV_NSCLIM_iff NSCLIM_def mem_infmal_iff [symmetric])
apply safe
apply (frule_tac f = g in NSCDERIV_approx)
apply (auto simp add: starfun_lambda_cancel2 starfun_o [symmetric])
apply (case_tac "( *f* g) (hcomplex_of_complex (x) + xa) = hcomplex_of_complex (g x) ")
apply (drule_tac g = g in NSCDERIV_zero)
apply (auto simp add: divide_inverse)
apply (rule_tac z1 = "( *f* g) (hcomplex_of_complex (x) + xa) - hcomplex_of_complex (g x) " and y1 = "inverse xa" in lemma_complex_chain [THEN ssubst])
apply (simp (no_asm_simp))
apply (rule approx_mult_hcomplex_of_complex)
apply (auto intro!: NSCDERIVD1 intro: approx_minus_iff [THEN iffD2] 
            simp add: diff_minus [symmetric] divide_inverse [symmetric])
apply (blast intro: NSCDERIVD2)
done

text{*standard version*}
lemma CDERIV_chain:
     "[| CDERIV f (g x) :> Da; CDERIV g x :> Db |]
      ==> CDERIV (f o g) x :> Da * Db"
by (simp add: NSCDERIV_CDERIV_iff [symmetric] NSCDERIV_chain)

lemma CDERIV_chain2:
     "[| CDERIV f (g x) :> Da; CDERIV g x :> Db |]
      ==> CDERIV (%x. f (g x)) x :> Da * Db"
by (auto dest: CDERIV_chain simp add: o_def)


subsection{* Differentiation of Natural Number Powers*}

lemma NSCDERIV_Id [simp]: "NSCDERIV (%x. x) x :> 1"
by (simp add: NSCDERIV_NSCLIM_iff NSCLIM_def divide_self del: divide_self_if)

lemma CDERIV_Id [simp]: "CDERIV (%x. x) x :> 1"
by (simp add: NSCDERIV_CDERIV_iff [symmetric])

lemmas isContc_Id = CDERIV_Id [THEN CDERIV_isContc, standard]

text{*derivative of linear multiplication*}
lemma CDERIV_cmult_Id [simp]: "CDERIV (op * c) x :> c"
by (cut_tac c = c and x = x in CDERIV_Id [THEN CDERIV_cmult], simp)

lemma NSCDERIV_cmult_Id [simp]: "NSCDERIV (op * c) x :> c"
by (simp add: NSCDERIV_CDERIV_iff)

lemma CDERIV_pow [simp]:
     "CDERIV (%x. x ^ n) x :> (complex_of_real (real n)) * (x ^ (n - Suc 0))"
apply (induct_tac "n")
apply (drule_tac [2] CDERIV_Id [THEN CDERIV_mult])
apply (auto simp add: left_distrib real_of_nat_Suc)
apply (case_tac "n")
apply (auto simp add: mult_ac add_commute)
done

text{*Nonstandard version*}
lemma NSCDERIV_pow:
     "NSCDERIV (%x. x ^ n) x :> complex_of_real (real n) * (x ^ (n - 1))"
by (simp add: NSCDERIV_CDERIV_iff)

lemma lemma_CDERIV_subst:
     "[|CDERIV f x :> D; D = E|] ==> CDERIV f x :> E"
by auto

(*used once, in NSCDERIV_inverse*)
lemma Infinitesimal_add_not_zero:
     "[| h: Infinitesimal; x \<noteq> 0 |] ==> hcomplex_of_complex x + h \<noteq> 0"
apply clarify
apply (drule equals_zero_I, auto)
done

text{*Can't relax the premise @{term "x \<noteq> 0"}: it isn't continuous at zero*}
lemma NSCDERIV_inverse:
     "x \<noteq> 0 ==> NSCDERIV (%x. inverse(x)) x :> (- (inverse x ^ 2))"
apply (simp add: nscderiv_def Ball_def, clarify) 
apply (frule Infinitesimal_add_not_zero [where x=x])
apply (auto simp add: starfun_inverse_inverse diff_minus 
           simp del: minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (simp add: add_commute numeral_2_eq_2 inverse_add
                 inverse_mult_distrib [symmetric] inverse_minus_eq [symmetric]
                 add_ac mult_ac 
            del: inverse_minus_eq inverse_mult_distrib
                 minus_mult_right [symmetric] minus_mult_left [symmetric])
apply (simp only: mult_assoc [symmetric] right_distrib)
apply (rule_tac y = " inverse (- hcomplex_of_complex x * hcomplex_of_complex x) " in approx_trans)
apply (rule inverse_add_Infinitesimal_approx2)
apply (auto dest!: hcomplex_of_complex_HFinite_diff_Infinitesimal 
            intro: HFinite_mult 
            simp add: inverse_minus_eq [symmetric] HFinite_minus_iff)
apply (rule Infinitesimal_HFinite_mult2, auto)
done

lemma CDERIV_inverse:
     "x \<noteq> 0 ==> CDERIV (%x. inverse(x)) x :> (-(inverse x ^ 2))"
by (simp add: NSCDERIV_inverse NSCDERIV_CDERIV_iff [symmetric] 
         del: complexpow_Suc)


subsection{*Derivative of Reciprocals (Function @{term inverse})*}

lemma CDERIV_inverse_fun:
     "[| CDERIV f x :> d; f(x) \<noteq> 0 |]
      ==> CDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ 2)))"
apply (rule mult_commute [THEN subst])
apply (simp add: minus_mult_left power_inverse
            del: complexpow_Suc minus_mult_left [symmetric])
apply (fold o_def)
apply (blast intro!: CDERIV_chain CDERIV_inverse)
done

lemma NSCDERIV_inverse_fun:
     "[| NSCDERIV f x :> d; f(x) \<noteq> 0 |]
      ==> NSCDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ 2)))"
by (simp add: NSCDERIV_CDERIV_iff CDERIV_inverse_fun del: complexpow_Suc)


subsection{* Derivative of Quotient*}

lemma CDERIV_quotient:
     "[| CDERIV f x :> d; CDERIV g x :> e; g(x) \<noteq> 0 |]
       ==> CDERIV (%y. f(y) / (g y)) x :> (d*g(x) - (e*f(x))) / (g(x) ^ 2)"
apply (simp add: diff_minus)
apply (drule_tac f = g in CDERIV_inverse_fun)
apply (drule_tac [2] CDERIV_mult, assumption+)
apply (simp add: divide_inverse left_distrib power_inverse minus_mult_left 
                 mult_ac 
            del: minus_mult_right [symmetric] minus_mult_left [symmetric]
                 complexpow_Suc)
done

lemma NSCDERIV_quotient:
     "[| NSCDERIV f x :> d; NSCDERIV g x :> e; g(x) \<noteq> 0 |]
       ==> NSCDERIV (%y. f(y) / (g y)) x :> (d*g(x) - (e*f(x))) / (g(x) ^ 2)"
by (simp add: NSCDERIV_CDERIV_iff CDERIV_quotient del: complexpow_Suc)


subsection{*Caratheodory Formulation of Derivative at a Point: Standard Proof*}

lemma CLIM_equal:
      "[| \<forall>x. x \<noteq> a --> (f x = g x) |] ==> (f -- a --C> l) = (g -- a --C> l)"
by (simp add: CLIM_def complex_add_minus_iff)

lemma CLIM_trans:
     "[| (%x. f(x) + -g(x)) -- a --C> 0; g -- a --C> l |] ==> f -- a --C> l"
apply (drule CLIM_add, assumption)
apply (simp add: complex_add_assoc)
done

lemma CARAT_CDERIV:
     "(CDERIV f x :> l) =
      (\<exists>g. (\<forall>z. f z - f x = g z * (z - x)) & isContc g x & g x = l)"
apply safe
apply (rule_tac x = "%z. if z=x then l else (f (z) - f (x)) / (z-x)" in exI)
apply (auto simp add: mult_assoc isContc_iff CDERIV_iff)
apply (rule_tac [!] CLIM_equal [THEN iffD1], auto)
done


lemma CARAT_NSCDERIV:
     "NSCDERIV f x :> l ==>
      \<exists>g. (\<forall>z. f z - f x = g z * (z - x)) & isNSContc g x & g x = l"
by (simp add: NSCDERIV_CDERIV_iff isNSContc_isContc_iff CARAT_CDERIV)

lemma CARAT_CDERIVD:
     "(\<forall>z. f z - f x = g z * (z - x)) & isNSContc g x & g x = l
      ==> NSCDERIV f x :> l"
by (auto simp add: NSCDERIV_iff2 isNSContc_def starfun_if_eq); 

end

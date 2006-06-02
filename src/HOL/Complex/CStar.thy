(*  Title       : CStar.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
*)

header{*Star-transforms in NSA, Extending Sets of Complex Numbers
      and Complex Functions*}

theory CStar
imports NSCA
begin

subsection{*Properties of the *-Transform Applied to Sets of Reals*}

lemma STARC_SComplex_subset: "SComplex \<subseteq> *s* (UNIV:: complex set)"
by simp

lemma STARC_hcomplex_of_complex_Int:
     "*s* X Int SComplex = hcomplex_of_complex ` X"
by (auto simp add: SComplex_def STAR_mem_iff)

lemma lemma_not_hcomplexA:
     "x \<notin> hcomplex_of_complex ` A ==> \<forall>y \<in> A. x \<noteq> hcomplex_of_complex y"
by auto

subsection{*Theorems about Nonstandard Extensions of Functions*}

lemma cstarfun_if_eq:
     "w \<noteq> hcomplex_of_complex x
       ==> ( *f* (\<lambda>z. if z = x then a else g z)) w = ( *f* g) w"
apply (cases w)
apply (simp add: star_of_def starfun star_n_eq_iff, ultra)
done

lemma starfun_capprox:
    "( *f* f) (hcomplex_of_complex a) @c= hcomplex_of_complex (f a)"
by auto

lemma starfunC_hcpow: "( *f* (%z. z ^ n)) Z = Z hcpow hypnat_of_nat n"
apply (cases Z)
apply (simp add: hcpow starfun hypnat_of_nat_eq)
done

lemma starfun_mult_CFinite_capprox:
    "[| ( *f* f) y @c= l; ( *f* g) y @c= m; l: CFinite; m: CFinite |]
     ==>  ( *f* (%x. f x * g x)) y @c= l * m"
apply (drule capprox_mult_CFinite, assumption+)
apply (auto intro: capprox_sym [THEN [2] capprox_CFinite])
done

lemma starfun_add_capprox:
    "[| ( *f* f) y @c= l; ( *f* g) y @c= m |]
     ==>  ( *f* (%x. f x + g x)) y @c= l + m"
by (auto intro: capprox_add)

lemma starfunCR_cmod: "*f* cmod = hcmod"
apply (rule ext)
apply (rule_tac x = x in star_cases)
apply (simp add: starfun hcmod)
done

subsection{*Internal Functions - Some Redundancy With *f* Now*}

(** subtraction: ( *fn) - ( *gn) = *(fn - gn) **)

lemma starfun_n_diff:
   "( *fn* f) z - ( *fn* g) z = ( *fn* (%i x. f i x - g i x)) z"
apply (cases z)
apply (simp add: starfun_n star_n_diff)
done

(** composition: ( *fn) o ( *gn) = *(fn o gn) **)

lemma starfunC_eq_Re_Im_iff:
    "(( *f* f) x = z) = ((( *f* (%x. Re(f x))) x = hRe (z)) &
                          (( *f* (%x. Im(f x))) x = hIm (z)))"
apply (cases x, cases z)
apply (auto simp add: starfun hIm hRe complex_Re_Im_cancel_iff star_n_eq_iff, ultra+)
done

lemma starfunC_approx_Re_Im_iff:
    "(( *f* f) x @c= z) = ((( *f* (%x. Re(f x))) x @= hRe (z)) &
                            (( *f* (%x. Im(f x))) x @= hIm (z)))"
apply (cases x, cases z)
apply (simp add: starfun hIm hRe capprox_approx_iff)
done

lemma starfunC_Idfun_capprox:
    "x @c= hcomplex_of_complex a ==> ( *f* (%x. x)) x @c= hcomplex_of_complex  a"
by simp

end

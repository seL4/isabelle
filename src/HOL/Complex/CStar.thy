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

lemma STARC_hcomplex_of_complex_Int:
     "*s* X Int SComplex = hcomplex_of_complex ` X"
by (auto simp add: Standard_def)

lemma lemma_not_hcomplexA:
     "x \<notin> hcomplex_of_complex ` A ==> \<forall>y \<in> A. x \<noteq> hcomplex_of_complex y"
by auto

subsection{*Theorems about Nonstandard Extensions of Functions*}

lemma starfunC_hcpow: "!!Z. ( *f* (%z. z ^ n)) Z = Z pow hypnat_of_nat n"
by transfer (rule refl)

lemma starfunCR_cmod: "*f* cmod = hcmod"
by transfer (rule refl)

subsection{*Internal Functions - Some Redundancy With *f* Now*}

(** subtraction: ( *fn) - ( *gn) = *(fn - gn) **)
(*
lemma starfun_n_diff:
   "( *fn* f) z - ( *fn* g) z = ( *fn* (%i x. f i x - g i x)) z"
apply (cases z)
apply (simp add: starfun_n star_n_diff)
done
*)
(** composition: ( *fn) o ( *gn) = *(fn o gn) **)

lemma starfun_Re: "( *f* (\<lambda>x. Re (f x))) = (\<lambda>x. hRe (( *f* f) x))"
by transfer (rule refl)

lemma starfun_Im: "( *f* (\<lambda>x. Im (f x))) = (\<lambda>x. hIm (( *f* f) x))"
by transfer (rule refl)

lemma starfunC_eq_Re_Im_iff:
    "(( *f* f) x = z) = ((( *f* (%x. Re(f x))) x = hRe (z)) &
                          (( *f* (%x. Im(f x))) x = hIm (z)))"
by (simp add: hcomplex_hRe_hIm_cancel_iff starfun_Re starfun_Im)

lemma starfunC_approx_Re_Im_iff:
    "(( *f* f) x @= z) = ((( *f* (%x. Re(f x))) x @= hRe (z)) &
                            (( *f* (%x. Im(f x))) x @= hIm (z)))"
by (simp add: hcomplex_approx_iff starfun_Re starfun_Im)

end

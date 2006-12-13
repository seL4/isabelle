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

lemma starfunC_hcpow: "( *f* (%z. z ^ n)) Z = Z hcpow hypnat_of_nat n"
apply (cases Z)
apply (simp add: hcpow starfun hypnat_of_nat_eq)
done

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
    "(( *f* f) x @= z) = ((( *f* (%x. Re(f x))) x @= hRe (z)) &
                            (( *f* (%x. Im(f x))) x @= hIm (z)))"
apply (cases x, cases z)
apply (simp add: starfun hIm hRe approx_approx_iff)
done

end

(*  Title:      HOL/Nonstandard_Analysis/CStar.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh
*)

section \<open>Star-transforms in NSA, Extending Sets of Complex Numbers and Complex Functions\<close>

theory CStar
  imports NSCA
begin

subsection \<open>Properties of the \<open>*\<close>-Transform Applied to Sets of Reals\<close>

lemma STARC_hcomplex_of_complex_Int: "*s* X \<inter> SComplex = hcomplex_of_complex ` X"
  by (auto simp: Standard_def)

lemma lemma_not_hcomplexA: "x \<notin> hcomplex_of_complex ` A \<Longrightarrow> \<forall>y \<in> A. x \<noteq> hcomplex_of_complex y"
  by auto


subsection \<open>Theorems about Nonstandard Extensions of Functions\<close>

lemma starfunC_hcpow: "\<And>Z. ( *f* (\<lambda>z. z ^ n)) Z = Z pow hypnat_of_nat n"
  by transfer (rule refl)

lemma starfunCR_cmod: "*f* cmod = hcmod"
  by transfer (rule refl)


subsection \<open>Internal Functions - Some Redundancy With \<open>*f*\<close> Now\<close>

(** subtraction: ( *fn) - ( *gn) = *(fn - gn) **)
(*
lemma starfun_n_diff:
   "( *fn* f) z - ( *fn* g) z = ( *fn* (\<lambda>i x. f i x - g i x)) z"
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
  "( *f* f) x = z \<longleftrightarrow> ( *f* (\<lambda>x. Re (f x))) x = hRe z \<and> ( *f* (\<lambda>x. Im (f x))) x = hIm z"
  by (simp add: hcomplex_hRe_hIm_cancel_iff starfun_Re starfun_Im)

lemma starfunC_approx_Re_Im_iff:
  "( *f* f) x \<approx> z \<longleftrightarrow> ( *f* (\<lambda>x. Re (f x))) x \<approx> hRe z \<and> ( *f* (\<lambda>x. Im (f x))) x \<approx> hIm z"
  by (simp add: hcomplex_approx_iff starfun_Re starfun_Im)

end

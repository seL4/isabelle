(*  Title:      HOL/Nonstandard_Analysis/CLim.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

section \<open>Limits, Continuity and Differentiation for Complex Functions\<close>

theory CLim
  imports CStar
begin

(*not in simpset?*)
declare hypreal_epsilon_not_zero [simp]

(*??generalize*)
lemma lemma_complex_mult_inverse_squared [simp]: "x \<noteq> 0 \<Longrightarrow> x * (inverse x)\<^sup>2 = inverse x"
  for x :: complex
  by (simp add: numeral_2_eq_2)

text \<open>Changing the quantified variable. Install earlier?\<close>
lemma all_shift: "(\<forall>x::'a::comm_ring_1. P x) \<longleftrightarrow> (\<forall>x. P (x - a))"
  apply auto
  apply (drule_tac x = "x + a" in spec)
  apply (simp add: add.assoc)
  done

lemma complex_add_minus_iff [simp]: "x + - a = 0 \<longleftrightarrow> x = a"
  for x a :: complex
  by (simp add: diff_eq_eq)

lemma complex_add_eq_0_iff [iff]: "x + y = 0 \<longleftrightarrow> y = - x"
  for x y :: complex
  apply auto
  apply (drule sym [THEN diff_eq_eq [THEN iffD2]])
  apply auto
  done


subsection \<open>Limit of Complex to Complex Function\<close>

lemma NSLIM_Re: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> (\<lambda>x. Re (f x)) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S Re L"
  by (simp add: NSLIM_def starfunC_approx_Re_Im_iff hRe_hcomplex_of_complex)

lemma NSLIM_Im: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> (\<lambda>x. Im (f x)) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S Im L"
  by (simp add: NSLIM_def starfunC_approx_Re_Im_iff hIm_hcomplex_of_complex)

lemma LIM_Re: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> (\<lambda>x. Re (f x)) \<midarrow>a\<rightarrow> Re L"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: LIM_NSLIM_iff NSLIM_Re)

lemma LIM_Im: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> (\<lambda>x. Im (f x)) \<midarrow>a\<rightarrow> Im L"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: LIM_NSLIM_iff NSLIM_Im)

lemma LIM_cnj: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> (\<lambda>x. cnj (f x)) \<midarrow>a\<rightarrow> cnj L"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: LIM_eq complex_cnj_diff [symmetric] del: complex_cnj_diff)

lemma LIM_cnj_iff: "((\<lambda>x. cnj (f x)) \<midarrow>a\<rightarrow> cnj L) \<longleftrightarrow> f \<midarrow>a\<rightarrow> L"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: LIM_eq complex_cnj_diff [symmetric] del: complex_cnj_diff)

lemma starfun_norm: "( *f* (\<lambda>x. norm (f x))) = (\<lambda>x. hnorm (( *f* f) x))"
  by transfer (rule refl)

lemma star_of_Re [simp]: "star_of (Re x) = hRe (star_of x)"
  by transfer (rule refl)

lemma star_of_Im [simp]: "star_of (Im x) = hIm (star_of x)"
  by transfer (rule refl)

text \<open>Another equivalence result.\<close>
lemma NSCLIM_NSCRLIM_iff: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S L \<longleftrightarrow> (\<lambda>y. cmod (f y - L)) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0"
  by (simp add: NSLIM_def starfun_norm
      approx_approx_zero_iff [symmetric] approx_minus_iff [symmetric])

text \<open>Much, much easier standard proof.\<close>
lemma CLIM_CRLIM_iff: "f \<midarrow>x\<rightarrow> L \<longleftrightarrow> (\<lambda>y. cmod (f y - L)) \<midarrow>x\<rightarrow> 0"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: LIM_eq)

text \<open>So this is nicer nonstandard proof.\<close>
lemma NSCLIM_NSCRLIM_iff2: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S L \<longleftrightarrow> (\<lambda>y. cmod (f y - L)) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0"
  by (simp add: LIM_NSLIM_iff [symmetric] CLIM_CRLIM_iff)

lemma NSLIM_NSCRLIM_Re_Im_iff:
  "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<longleftrightarrow> (\<lambda>x. Re (f x)) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S Re L \<and> (\<lambda>x. Im (f x)) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S Im L"
  apply (auto intro: NSLIM_Re NSLIM_Im)
  apply (auto simp add: NSLIM_def starfun_Re starfun_Im)
  apply (auto dest!: spec)
  apply (simp add: hcomplex_approx_iff)
  done

lemma LIM_CRLIM_Re_Im_iff: "f \<midarrow>a\<rightarrow> L \<longleftrightarrow> (\<lambda>x. Re (f x)) \<midarrow>a\<rightarrow> Re L \<and> (\<lambda>x. Im (f x)) \<midarrow>a\<rightarrow> Im L"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: LIM_NSLIM_iff NSLIM_NSCRLIM_Re_Im_iff)


subsection \<open>Continuity\<close>

lemma NSLIM_isContc_iff: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S f a \<longleftrightarrow> (\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S f a"
  by (rule NSLIM_h_iff)


subsection \<open>Functions from Complex to Reals\<close>

lemma isNSContCR_cmod [simp]: "isNSCont cmod a"
  by (auto intro: approx_hnorm
      simp: starfunCR_cmod hcmod_hcomplex_of_complex [symmetric] isNSCont_def)

lemma isContCR_cmod [simp]: "isCont cmod a"
  by (simp add: isNSCont_isCont_iff [symmetric])

lemma isCont_Re: "isCont f a \<Longrightarrow> isCont (\<lambda>x. Re (f x)) a"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: isCont_def LIM_Re)

lemma isCont_Im: "isCont f a \<Longrightarrow> isCont (\<lambda>x. Im (f x)) a"
  for f :: "'a::real_normed_vector \<Rightarrow> complex"
  by (simp add: isCont_def LIM_Im)


subsection \<open>Differentiation of Natural Number Powers\<close>

lemma CDERIV_pow [simp]: "DERIV (\<lambda>x. x ^ n) x :> complex_of_real (real n) * (x ^ (n - Suc 0))"
  apply (induct n)
   apply (drule_tac [2] DERIV_ident [THEN DERIV_mult])
   apply (auto simp add: distrib_right of_nat_Suc)
  apply (case_tac "n")
   apply (auto simp add: ac_simps)
  done

text \<open>Nonstandard version.\<close>
lemma NSCDERIV_pow: "NSDERIV (\<lambda>x. x ^ n) x :> complex_of_real (real n) * (x ^ (n - 1))"
  by (metis CDERIV_pow NSDERIV_DERIV_iff One_nat_def)

text \<open>Can't relax the premise \<^term>\<open>x \<noteq> 0\<close>: it isn't continuous at zero.\<close>
lemma NSCDERIV_inverse: "x \<noteq> 0 \<Longrightarrow> NSDERIV (\<lambda>x. inverse x) x :> - (inverse x)\<^sup>2"
  for x :: complex
  unfolding numeral_2_eq_2 by (rule NSDERIV_inverse)

lemma CDERIV_inverse: "x \<noteq> 0 \<Longrightarrow> DERIV (\<lambda>x. inverse x) x :> - (inverse x)\<^sup>2"
  for x :: complex
  unfolding numeral_2_eq_2 by (rule DERIV_inverse)


subsection \<open>Derivative of Reciprocals (Function \<^term>\<open>inverse\<close>)\<close>

lemma CDERIV_inverse_fun:
  "DERIV f x :> d \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> DERIV (\<lambda>x. inverse (f x)) x :> - (d * inverse ((f x)\<^sup>2))"
  for x :: complex
  unfolding numeral_2_eq_2 by (rule DERIV_inverse_fun)

lemma NSCDERIV_inverse_fun:
  "NSDERIV f x :> d \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> NSDERIV (\<lambda>x. inverse (f x)) x :> - (d * inverse ((f x)\<^sup>2))"
  for x :: complex
  unfolding numeral_2_eq_2 by (rule NSDERIV_inverse_fun)


subsection \<open>Derivative of Quotient\<close>

lemma CDERIV_quotient:
  "DERIV f x :> d \<Longrightarrow> DERIV g x :> e \<Longrightarrow> g(x) \<noteq> 0 \<Longrightarrow>
    DERIV (\<lambda>y. f y / g y) x :> (d * g x - (e * f x)) / (g x)\<^sup>2"
  for x :: complex
  unfolding numeral_2_eq_2 by (rule DERIV_quotient)

lemma NSCDERIV_quotient:
  "NSDERIV f x :> d \<Longrightarrow> NSDERIV g x :> e \<Longrightarrow> g x \<noteq> (0::complex) \<Longrightarrow>
    NSDERIV (\<lambda>y. f y / g y) x :> (d * g x - (e * f x)) / (g x)\<^sup>2"
  unfolding numeral_2_eq_2 by (rule NSDERIV_quotient)


subsection \<open>Caratheodory Formulation of Derivative at a Point: Standard Proof\<close>

lemma CARAT_CDERIVD:
  "(\<forall>z. f z - f x = g z * (z - x)) \<and> isNSCont g x \<and> g x = l \<Longrightarrow> NSDERIV f x :> l"
  by clarify (rule CARAT_DERIVD)

end

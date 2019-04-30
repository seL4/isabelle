(*  Title:      HOL/Nonstandard_Analysis/NSCA.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2001, 2002 University of Edinburgh
*)

section\<open>Non-Standard Complex Analysis\<close>

theory NSCA
imports NSComplex HTranscendental
begin

abbreviation
   (* standard complex numbers reagarded as an embedded subset of NS complex *)
   SComplex  :: "hcomplex set" where
   "SComplex \<equiv> Standard"

definition \<comment> \<open>standard part map\<close>
  stc :: "hcomplex => hcomplex" where 
  "stc x = (SOME r. x \<in> HFinite \<and> r\<in>SComplex \<and> r \<approx> x)"


subsection\<open>Closure Laws for SComplex, the Standard Complex Numbers\<close>

lemma SComplex_minus_iff [simp]: "(-x \<in> SComplex) = (x \<in> SComplex)"
  using Standard_minus by fastforce

lemma SComplex_add_cancel:
  "\<lbrakk>x + y \<in> SComplex; y \<in> SComplex\<rbrakk> \<Longrightarrow> x \<in> SComplex"
  using Standard_diff by fastforce

lemma SReal_hcmod_hcomplex_of_complex [simp]:
  "hcmod (hcomplex_of_complex r) \<in> \<real>"
  by (simp add: Reals_eq_Standard)

lemma SReal_hcmod_numeral: "hcmod (numeral w ::hcomplex) \<in> \<real>"
  by simp

lemma SReal_hcmod_SComplex: "x \<in> SComplex \<Longrightarrow> hcmod x \<in> \<real>"
  by (simp add: Reals_eq_Standard)

lemma SComplex_divide_numeral:
  "r \<in> SComplex \<Longrightarrow> r/(numeral w::hcomplex) \<in> SComplex"
  by simp

lemma SComplex_UNIV_complex:
  "{x. hcomplex_of_complex x \<in> SComplex} = (UNIV::complex set)"
  by simp

lemma SComplex_iff: "(x \<in> SComplex) = (\<exists>y. x = hcomplex_of_complex y)"
  by (simp add: Standard_def image_def)

lemma hcomplex_of_complex_image:
  "range hcomplex_of_complex = SComplex"
  by (simp add: Standard_def)

lemma inv_hcomplex_of_complex_image: "inv hcomplex_of_complex `SComplex = UNIV"
by (auto simp add: Standard_def image_def) (metis inj_star_of inv_f_f)

lemma SComplex_hcomplex_of_complex_image: 
      "\<lbrakk>\<exists>x. x \<in> P; P \<le> SComplex\<rbrakk> \<Longrightarrow> \<exists>Q. P = hcomplex_of_complex ` Q"
  by (metis Standard_def subset_imageE)

lemma SComplex_SReal_dense:
     "\<lbrakk>x \<in> SComplex; y \<in> SComplex; hcmod x < hcmod y  
      \<rbrakk> \<Longrightarrow> \<exists>r \<in> Reals. hcmod x< r \<and> r < hcmod y"
  by (simp add: SReal_dense SReal_hcmod_SComplex)


subsection\<open>The Finite Elements form a Subring\<close>

lemma HFinite_hcmod_hcomplex_of_complex [simp]:
  "hcmod (hcomplex_of_complex r) \<in> HFinite"
  by (auto intro!: SReal_subset_HFinite [THEN subsetD])

lemma HFinite_hcmod_iff [simp]: "hcmod x \<in> HFinite \<longleftrightarrow> x \<in> HFinite"
  by (simp add: HFinite_def)

lemma HFinite_bounded_hcmod:
  "\<lbrakk>x \<in> HFinite; y \<le> hcmod x; 0 \<le> y\<rbrakk> \<Longrightarrow> y \<in> HFinite"
  using HFinite_bounded HFinite_hcmod_iff by blast


subsection\<open>The Complex Infinitesimals form a Subring\<close>

lemma Infinitesimal_hcmod_iff: 
  "(z \<in> Infinitesimal) = (hcmod z \<in> Infinitesimal)"
  by (simp add: Infinitesimal_def)

lemma HInfinite_hcmod_iff: "(z \<in> HInfinite) = (hcmod z \<in> HInfinite)"
  by (simp add: HInfinite_def)

lemma HFinite_diff_Infinitesimal_hcmod:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> hcmod x \<in> HFinite - Infinitesimal"
  by (simp add: Infinitesimal_hcmod_iff)

lemma hcmod_less_Infinitesimal:
  "\<lbrakk>e \<in> Infinitesimal; hcmod x < hcmod e\<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
  by (auto elim: hrabs_less_Infinitesimal simp add: Infinitesimal_hcmod_iff)

lemma hcmod_le_Infinitesimal:
  "\<lbrakk>e \<in> Infinitesimal; hcmod x \<le> hcmod e\<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
  by (auto elim: hrabs_le_Infinitesimal simp add: Infinitesimal_hcmod_iff)


subsection\<open>The ``Infinitely Close'' Relation\<close>

lemma approx_SComplex_mult_cancel_zero:
  "\<lbrakk>a \<in> SComplex; a \<noteq> 0; a*x \<approx> 0\<rbrakk> \<Longrightarrow> x \<approx> 0"
  by (metis Infinitesimal_mult_disj SComplex_iff mem_infmal_iff star_of_Infinitesimal_iff_0 star_zero_def)

lemma approx_mult_SComplex1: "\<lbrakk>a \<in> SComplex; x \<approx> 0\<rbrakk> \<Longrightarrow> x*a \<approx> 0"
  using SComplex_iff approx_mult_subst_star_of by fastforce

lemma approx_mult_SComplex2: "\<lbrakk>a \<in> SComplex; x \<approx> 0\<rbrakk> \<Longrightarrow> a*x \<approx> 0"
  by (metis approx_mult_SComplex1 mult.commute)

lemma approx_mult_SComplex_zero_cancel_iff [simp]:
  "\<lbrakk>a \<in> SComplex; a \<noteq> 0\<rbrakk> \<Longrightarrow> (a*x \<approx> 0) = (x \<approx> 0)"
  using approx_SComplex_mult_cancel_zero approx_mult_SComplex2 by blast

lemma approx_SComplex_mult_cancel:
     "\<lbrakk>a \<in> SComplex; a \<noteq> 0; a*w \<approx> a*z\<rbrakk> \<Longrightarrow> w \<approx> z"
  by (metis approx_SComplex_mult_cancel_zero approx_minus_iff right_diff_distrib)

lemma approx_SComplex_mult_cancel_iff1 [simp]:
     "\<lbrakk>a \<in> SComplex; a \<noteq> 0\<rbrakk> \<Longrightarrow> (a*w \<approx> a*z) = (w \<approx> z)"
  by (metis HFinite_star_of SComplex_iff approx_SComplex_mult_cancel approx_mult2)

(* TODO: generalize following theorems: hcmod -> hnorm *)

lemma approx_hcmod_approx_zero: "(x \<approx> y) = (hcmod (y - x) \<approx> 0)"
  by (simp add: Infinitesimal_hcmod_iff approx_def hnorm_minus_commute)

lemma approx_approx_zero_iff: "(x \<approx> 0) = (hcmod x \<approx> 0)"
by (simp add: approx_hcmod_approx_zero)

lemma approx_minus_zero_cancel_iff [simp]: "(-x \<approx> 0) = (x \<approx> 0)"
by (simp add: approx_def)

lemma Infinitesimal_hcmod_add_diff:
     "u \<approx> 0 \<Longrightarrow> hcmod(x + u) - hcmod x \<in> Infinitesimal"
  by (metis add.commute add.left_neutral approx_add_right_iff approx_def approx_hnorm)

lemma approx_hcmod_add_hcmod: "u \<approx> 0 \<Longrightarrow> hcmod(x + u) \<approx> hcmod x"
  using Infinitesimal_hcmod_add_diff approx_def by blast


subsection\<open>Zero is the Only Infinitesimal Complex Number\<close>

lemma Infinitesimal_less_SComplex:
  "\<lbrakk>x \<in> SComplex; y \<in> Infinitesimal; 0 < hcmod x\<rbrakk> \<Longrightarrow> hcmod y < hcmod x"
  by (auto intro: Infinitesimal_less_SReal SReal_hcmod_SComplex simp add: Infinitesimal_hcmod_iff)

lemma SComplex_Int_Infinitesimal_zero: "SComplex Int Infinitesimal = {0}"
  by (auto simp add: Standard_def Infinitesimal_hcmod_iff)

lemma SComplex_Infinitesimal_zero:
  "\<lbrakk>x \<in> SComplex; x \<in> Infinitesimal\<rbrakk> \<Longrightarrow> x = 0"
  using SComplex_iff by auto

lemma SComplex_HFinite_diff_Infinitesimal:
  "\<lbrakk>x \<in> SComplex; x \<noteq> 0\<rbrakk> \<Longrightarrow> x \<in> HFinite - Infinitesimal"
  using SComplex_iff by auto

lemma numeral_not_Infinitesimal [simp]:
  "numeral w \<noteq> (0::hcomplex) \<Longrightarrow> (numeral w::hcomplex) \<notin> Infinitesimal"
  by (fast dest: Standard_numeral [THEN SComplex_Infinitesimal_zero])

lemma approx_SComplex_not_zero:
  "\<lbrakk>y \<in> SComplex; x \<approx> y; y\<noteq> 0\<rbrakk> \<Longrightarrow> x \<noteq> 0"
  by (auto dest: SComplex_Infinitesimal_zero approx_sym [THEN mem_infmal_iff [THEN iffD2]])

lemma SComplex_approx_iff:
  "\<lbrakk>x \<in> SComplex; y \<in> SComplex\<rbrakk> \<Longrightarrow> (x \<approx> y) = (x = y)"
  by (auto simp add: Standard_def)

lemma approx_unique_complex:
  "\<lbrakk>r \<in> SComplex; s \<in> SComplex; r \<approx> x; s \<approx> x\<rbrakk> \<Longrightarrow> r = s"
  by (blast intro: SComplex_approx_iff [THEN iffD1] approx_trans2)

subsection \<open>Properties of \<^term>\<open>hRe\<close>, \<^term>\<open>hIm\<close> and \<^term>\<open>HComplex\<close>\<close>

lemma abs_hRe_le_hcmod: "\<And>x. \<bar>hRe x\<bar> \<le> hcmod x"
  by transfer (rule abs_Re_le_cmod)

lemma abs_hIm_le_hcmod: "\<And>x. \<bar>hIm x\<bar> \<le> hcmod x"
  by transfer (rule abs_Im_le_cmod)

lemma Infinitesimal_hRe: "x \<in> Infinitesimal \<Longrightarrow> hRe x \<in> Infinitesimal"
  using Infinitesimal_hcmod_iff abs_hRe_le_hcmod hrabs_le_Infinitesimal by blast

lemma Infinitesimal_hIm: "x \<in> Infinitesimal \<Longrightarrow> hIm x \<in> Infinitesimal"
  using Infinitesimal_hcmod_iff abs_hIm_le_hcmod hrabs_le_Infinitesimal by blast

lemma Infinitesimal_HComplex:
  assumes x: "x \<in> Infinitesimal" and y: "y \<in> Infinitesimal"
  shows "HComplex x y \<in> Infinitesimal"
proof -
  have "hcmod (HComplex 0 y) \<in> Infinitesimal"
    by (simp add: hcmod_i y)
  moreover have "hcmod (hcomplex_of_hypreal x) \<in> Infinitesimal" 
    using Infinitesimal_hcmod_iff Infinitesimal_of_hypreal_iff x by blast
  ultimately have "hcmod (HComplex x y) \<in> Infinitesimal"
    by (metis Infinitesimal_add Infinitesimal_hcmod_iff add.right_neutral hcomplex_of_hypreal_add_HComplex)
  then show ?thesis
    by (simp add: Infinitesimal_hnorm_iff)
qed

lemma hcomplex_Infinitesimal_iff:
  "(x \<in> Infinitesimal) \<longleftrightarrow> (hRe x \<in> Infinitesimal \<and> hIm x \<in> Infinitesimal)"
  using Infinitesimal_HComplex Infinitesimal_hIm Infinitesimal_hRe by fastforce

lemma hRe_diff [simp]: "\<And>x y. hRe (x - y) = hRe x - hRe y"
  by transfer simp

lemma hIm_diff [simp]: "\<And>x y. hIm (x - y) = hIm x - hIm y"
  by transfer simp

lemma approx_hRe: "x \<approx> y \<Longrightarrow> hRe x \<approx> hRe y"
  unfolding approx_def by (drule Infinitesimal_hRe) simp

lemma approx_hIm: "x \<approx> y \<Longrightarrow> hIm x \<approx> hIm y"
  unfolding approx_def by (drule Infinitesimal_hIm) simp

lemma approx_HComplex:
  "\<lbrakk>a \<approx> b; c \<approx> d\<rbrakk> \<Longrightarrow> HComplex a c \<approx> HComplex b d"
  unfolding approx_def by (simp add: Infinitesimal_HComplex)

lemma hcomplex_approx_iff:
  "(x \<approx> y) = (hRe x \<approx> hRe y \<and> hIm x \<approx> hIm y)"
  unfolding approx_def by (simp add: hcomplex_Infinitesimal_iff)

lemma HFinite_hRe: "x \<in> HFinite \<Longrightarrow> hRe x \<in> HFinite"
  using HFinite_bounded_hcmod abs_ge_zero abs_hRe_le_hcmod by blast

lemma HFinite_hIm: "x \<in> HFinite \<Longrightarrow> hIm x \<in> HFinite"
  using HFinite_bounded_hcmod abs_ge_zero abs_hIm_le_hcmod by blast

lemma HFinite_HComplex:
  assumes "x \<in> HFinite" "y \<in> HFinite"
  shows "HComplex x y \<in> HFinite"
proof -
  have "HComplex x 0 \<in> HFinite" "HComplex 0 y \<in> HFinite"
    using HFinite_hcmod_iff assms hcmod_i by fastforce+
  then have "HComplex x 0 + HComplex 0 y \<in> HFinite"
    using HFinite_add by blast
  then show ?thesis
    by simp
qed

lemma hcomplex_HFinite_iff:
  "(x \<in> HFinite) = (hRe x \<in> HFinite \<and> hIm x \<in> HFinite)"
  using HFinite_HComplex HFinite_hIm HFinite_hRe by fastforce

lemma hcomplex_HInfinite_iff:
  "(x \<in> HInfinite) = (hRe x \<in> HInfinite \<or> hIm x \<in> HInfinite)"
  by (simp add: HInfinite_HFinite_iff hcomplex_HFinite_iff)

lemma hcomplex_of_hypreal_approx_iff [simp]:
  "(hcomplex_of_hypreal x \<approx> hcomplex_of_hypreal z) = (x \<approx> z)"
  by (simp add: hcomplex_approx_iff)

(* Here we go - easy proof now!! *)
lemma stc_part_Ex:
  assumes "x \<in> HFinite" 
  shows "\<exists>t \<in> SComplex. x \<approx> t"
proof -
  let ?t = "HComplex (st (hRe x)) (st (hIm x))"
  have "?t \<in> SComplex"
    using HFinite_hIm HFinite_hRe Reals_eq_Standard assms st_SReal by auto
  moreover have "x \<approx> ?t"
    by (simp add: HFinite_hIm HFinite_hRe assms hcomplex_approx_iff st_HFinite st_eq_approx)
  ultimately show ?thesis ..
qed

lemma stc_part_Ex1: "x \<in> HFinite \<Longrightarrow> \<exists>!t. t \<in> SComplex \<and> x \<approx> t"
  using approx_sym approx_unique_complex stc_part_Ex by blast


subsection\<open>Theorems About Monads\<close>

lemma monad_zero_hcmod_iff: "(x \<in> monad 0) = (hcmod x \<in> monad 0)"
  by (simp add: Infinitesimal_monad_zero_iff [symmetric] Infinitesimal_hcmod_iff)


subsection\<open>Theorems About Standard Part\<close>

lemma stc_approx_self: "x \<in> HFinite \<Longrightarrow> stc x \<approx> x"
  unfolding stc_def
  by (metis (no_types, lifting) approx_reorient someI_ex stc_part_Ex1)

lemma stc_SComplex: "x \<in> HFinite \<Longrightarrow> stc x \<in> SComplex"
  unfolding stc_def
  by (metis (no_types, lifting) SComplex_iff approx_sym someI_ex stc_part_Ex)

lemma stc_HFinite: "x \<in> HFinite \<Longrightarrow> stc x \<in> HFinite"
  by (erule stc_SComplex [THEN Standard_subset_HFinite [THEN subsetD]])

lemma stc_unique: "\<lbrakk>y \<in> SComplex; y \<approx> x\<rbrakk> \<Longrightarrow> stc x = y"
  by (metis SComplex_approx_iff SComplex_iff approx_monad_iff approx_star_of_HFinite stc_SComplex stc_approx_self)

lemma stc_SComplex_eq [simp]: "x \<in> SComplex \<Longrightarrow> stc x = x"
  by (simp add: stc_unique)

lemma stc_eq_approx:
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite; stc x = stc y\<rbrakk> \<Longrightarrow> x \<approx> y"
  by (auto dest!: stc_approx_self elim!: approx_trans3)

lemma approx_stc_eq:
     "\<lbrakk>x \<in> HFinite; y \<in> HFinite; x \<approx> y\<rbrakk> \<Longrightarrow> stc x = stc y"
  by (metis approx_sym approx_trans3 stc_part_Ex1 stc_unique)

lemma stc_eq_approx_iff:
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> (x \<approx> y) = (stc x = stc y)"
  by (blast intro: approx_stc_eq stc_eq_approx)

lemma stc_Infinitesimal_add_SComplex:
  "\<lbrakk>x \<in> SComplex; e \<in> Infinitesimal\<rbrakk> \<Longrightarrow> stc(x + e) = x"
  using Infinitesimal_add_approx_self stc_unique by blast

lemma stc_Infinitesimal_add_SComplex2:
  "\<lbrakk>x \<in> SComplex; e \<in> Infinitesimal\<rbrakk> \<Longrightarrow> stc(e + x) = x"
  using Infinitesimal_add_approx_self2 stc_unique by blast

lemma HFinite_stc_Infinitesimal_add:
  "x \<in> HFinite \<Longrightarrow> \<exists>e \<in> Infinitesimal. x = stc(x) + e"
  by (blast dest!: stc_approx_self [THEN approx_sym] bex_Infinitesimal_iff2 [THEN iffD2])

lemma stc_add:
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> stc (x + y) = stc(x) + stc(y)"
  by (simp add: stc_unique stc_SComplex stc_approx_self approx_add)

lemma stc_zero: "stc 0 = 0"
  by simp

lemma stc_one: "stc 1 = 1"
  by simp

lemma stc_minus: "y \<in> HFinite \<Longrightarrow> stc(-y) = -stc(y)"
  by (simp add: stc_unique stc_SComplex stc_approx_self approx_minus)

lemma stc_diff: 
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> stc (x-y) = stc(x) - stc(y)"
  by (simp add: stc_unique stc_SComplex stc_approx_self approx_diff)

lemma stc_mult:
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk>  
               \<Longrightarrow> stc (x * y) = stc(x) * stc(y)"
  by (simp add: stc_unique stc_SComplex stc_approx_self approx_mult_HFinite)

lemma stc_Infinitesimal: "x \<in> Infinitesimal \<Longrightarrow> stc x = 0"
  by (simp add: stc_unique mem_infmal_iff)

lemma stc_not_Infinitesimal: "stc(x) \<noteq> 0 \<Longrightarrow> x \<notin> Infinitesimal"
  by (fast intro: stc_Infinitesimal)

lemma stc_inverse:
  "\<lbrakk>x \<in> HFinite; stc x \<noteq> 0\<rbrakk>  \<Longrightarrow> stc(inverse x) = inverse (stc x)"
  by (simp add: stc_unique stc_SComplex stc_approx_self approx_inverse stc_not_Infinitesimal)

lemma stc_divide [simp]:
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite; stc y \<noteq> 0\<rbrakk>  
      \<Longrightarrow> stc(x/y) = (stc x) / (stc y)"
  by (simp add: divide_inverse stc_mult stc_not_Infinitesimal HFinite_inverse stc_inverse)

lemma stc_idempotent [simp]: "x \<in> HFinite \<Longrightarrow> stc(stc(x)) = stc(x)"
  by (blast intro: stc_HFinite stc_approx_self approx_stc_eq)

lemma HFinite_HFinite_hcomplex_of_hypreal:
  "z \<in> HFinite \<Longrightarrow> hcomplex_of_hypreal z \<in> HFinite"
  by (simp add: hcomplex_HFinite_iff)

lemma SComplex_SReal_hcomplex_of_hypreal:
     "x \<in> \<real> \<Longrightarrow>  hcomplex_of_hypreal x \<in> SComplex"
  by (simp add: Reals_eq_Standard)

lemma stc_hcomplex_of_hypreal: 
 "z \<in> HFinite \<Longrightarrow> stc(hcomplex_of_hypreal z) = hcomplex_of_hypreal (st z)"
  by (simp add: SComplex_SReal_hcomplex_of_hypreal st_SReal st_approx_self stc_unique)

lemma hmod_stc_eq:
  assumes "x \<in> HFinite" 
  shows "hcmod(stc x) = st(hcmod x)"
    by (metis SReal_hcmod_SComplex approx_HFinite approx_hnorm assms st_unique stc_SComplex_eq stc_eq_approx_iff stc_part_Ex)

lemma Infinitesimal_hcnj_iff [simp]:
  "(hcnj z \<in> Infinitesimal) \<longleftrightarrow> (z \<in> Infinitesimal)"
  by (simp add: Infinitesimal_hcmod_iff)

end

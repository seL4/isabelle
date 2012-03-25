(*  Title       : NSA/NSCA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001,2002 University of Edinburgh
*)

header{*Non-Standard Complex Analysis*}

theory NSCA
imports NSComplex HTranscendental
begin

abbreviation
   (* standard complex numbers reagarded as an embedded subset of NS complex *)
   SComplex  :: "hcomplex set" where
   "SComplex \<equiv> Standard"

definition --{* standard part map*}
  stc :: "hcomplex => hcomplex" where 
  "stc x = (SOME r. x \<in> HFinite & r:SComplex & r @= x)"


subsection{*Closure Laws for SComplex, the Standard Complex Numbers*}

lemma SComplex_minus_iff [simp]: "(-x \<in> SComplex) = (x \<in> SComplex)"
by (auto, drule Standard_minus, auto)

lemma SComplex_add_cancel:
     "[| x + y \<in> SComplex; y \<in> SComplex |] ==> x \<in> SComplex"
by (drule (1) Standard_diff, simp)

lemma SReal_hcmod_hcomplex_of_complex [simp]:
     "hcmod (hcomplex_of_complex r) \<in> Reals"
by (simp add: Reals_eq_Standard)

lemma SReal_hcmod_numeral [simp]: "hcmod (numeral w ::hcomplex) \<in> Reals"
by (simp add: Reals_eq_Standard)

lemma SReal_hcmod_SComplex: "x \<in> SComplex ==> hcmod x \<in> Reals"
by (simp add: Reals_eq_Standard)

lemma SComplex_divide_numeral:
     "r \<in> SComplex ==> r/(numeral w::hcomplex) \<in> SComplex"
by simp

lemma SComplex_UNIV_complex:
     "{x. hcomplex_of_complex x \<in> SComplex} = (UNIV::complex set)"
by simp

lemma SComplex_iff: "(x \<in> SComplex) = (\<exists>y. x = hcomplex_of_complex y)"
by (simp add: Standard_def image_def)

lemma hcomplex_of_complex_image:
     "hcomplex_of_complex `(UNIV::complex set) = SComplex"
by (simp add: Standard_def)

lemma inv_hcomplex_of_complex_image: "inv hcomplex_of_complex `SComplex = UNIV"
apply (auto simp add: Standard_def image_def)
apply (rule inj_hcomplex_of_complex [THEN inv_f_f, THEN subst], blast)
done

lemma SComplex_hcomplex_of_complex_image: 
      "[| \<exists>x. x: P; P \<le> SComplex |] ==> \<exists>Q. P = hcomplex_of_complex ` Q"
apply (simp add: Standard_def, blast)
done

lemma SComplex_SReal_dense:
     "[| x \<in> SComplex; y \<in> SComplex; hcmod x < hcmod y  
      |] ==> \<exists>r \<in> Reals. hcmod x< r & r < hcmod y"
apply (auto intro: SReal_dense simp add: SReal_hcmod_SComplex)
done

lemma SComplex_hcmod_SReal: 
      "z \<in> SComplex ==> hcmod z \<in> Reals"
by (simp add: Reals_eq_Standard)


subsection{*The Finite Elements form a Subring*}

lemma HFinite_hcmod_hcomplex_of_complex [simp]:
     "hcmod (hcomplex_of_complex r) \<in> HFinite"
by (auto intro!: SReal_subset_HFinite [THEN subsetD])

lemma HFinite_hcmod_iff: "(x \<in> HFinite) = (hcmod x \<in> HFinite)"
by (simp add: HFinite_def)

lemma HFinite_bounded_hcmod:
  "[|x \<in> HFinite; y \<le> hcmod x; 0 \<le> y |] ==> y: HFinite"
by (auto intro: HFinite_bounded simp add: HFinite_hcmod_iff)


subsection{*The Complex Infinitesimals form a Subring*}

lemma hcomplex_sum_of_halves: "x/(2::hcomplex) + x/(2::hcomplex) = x"
by auto

lemma Infinitesimal_hcmod_iff: 
   "(z \<in> Infinitesimal) = (hcmod z \<in> Infinitesimal)"
by (simp add: Infinitesimal_def)

lemma HInfinite_hcmod_iff: "(z \<in> HInfinite) = (hcmod z \<in> HInfinite)"
by (simp add: HInfinite_def)

lemma HFinite_diff_Infinitesimal_hcmod:
     "x \<in> HFinite - Infinitesimal ==> hcmod x \<in> HFinite - Infinitesimal"
by (simp add: HFinite_hcmod_iff Infinitesimal_hcmod_iff)

lemma hcmod_less_Infinitesimal:
     "[| e \<in> Infinitesimal; hcmod x < hcmod e |] ==> x \<in> Infinitesimal"
by (auto elim: hrabs_less_Infinitesimal simp add: Infinitesimal_hcmod_iff)

lemma hcmod_le_Infinitesimal:
     "[| e \<in> Infinitesimal; hcmod x \<le> hcmod e |] ==> x \<in> Infinitesimal"
by (auto elim: hrabs_le_Infinitesimal simp add: Infinitesimal_hcmod_iff)

lemma Infinitesimal_interval_hcmod:
     "[| e \<in> Infinitesimal;  
          e' \<in> Infinitesimal;  
          hcmod e' < hcmod x ; hcmod x < hcmod e  
       |] ==> x \<in> Infinitesimal"
by (auto intro: Infinitesimal_interval simp add: Infinitesimal_hcmod_iff)

lemma Infinitesimal_interval2_hcmod:
     "[| e \<in> Infinitesimal;  
         e' \<in> Infinitesimal;  
         hcmod e' \<le> hcmod x ; hcmod x \<le> hcmod e  
      |] ==> x \<in> Infinitesimal"
by (auto intro: Infinitesimal_interval2 simp add: Infinitesimal_hcmod_iff)


subsection{*The ``Infinitely Close'' Relation*}

(*
Goalw [capprox_def,approx_def] "(z @c= w) = (hcmod z @= hcmod w)"
by (auto_tac (claset(),simpset() addsimps [Infinitesimal_hcmod_iff]));
*)

lemma approx_SComplex_mult_cancel_zero:
     "[| a \<in> SComplex; a \<noteq> 0; a*x @= 0 |] ==> x @= 0"
apply (drule Standard_inverse [THEN Standard_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_mult_SComplex1: "[| a \<in> SComplex; x @= 0 |] ==> x*a @= 0"
by (auto dest: Standard_subset_HFinite [THEN subsetD] approx_mult1)

lemma approx_mult_SComplex2: "[| a \<in> SComplex; x @= 0 |] ==> a*x @= 0"
by (auto dest: Standard_subset_HFinite [THEN subsetD] approx_mult2)

lemma approx_mult_SComplex_zero_cancel_iff [simp]:
     "[|a \<in> SComplex; a \<noteq> 0 |] ==> (a*x @= 0) = (x @= 0)"
by (blast intro: approx_SComplex_mult_cancel_zero approx_mult_SComplex2)

lemma approx_SComplex_mult_cancel:
     "[| a \<in> SComplex; a \<noteq> 0; a* w @= a*z |] ==> w @= z"
apply (drule Standard_inverse [THEN Standard_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_SComplex_mult_cancel_iff1 [simp]:
     "[| a \<in> SComplex; a \<noteq> 0|] ==> (a* w @= a*z) = (w @= z)"
by (auto intro!: approx_mult2 Standard_subset_HFinite [THEN subsetD]
            intro: approx_SComplex_mult_cancel)

(* TODO: generalize following theorems: hcmod -> hnorm *)

lemma approx_hcmod_approx_zero: "(x @= y) = (hcmod (y - x) @= 0)"
apply (subst hnorm_minus_commute)
apply (simp add: approx_def Infinitesimal_hcmod_iff diff_minus)
done

lemma approx_approx_zero_iff: "(x @= 0) = (hcmod x @= 0)"
by (simp add: approx_hcmod_approx_zero)

lemma approx_minus_zero_cancel_iff [simp]: "(-x @= 0) = (x @= 0)"
by (simp add: approx_def)

lemma Infinitesimal_hcmod_add_diff:
     "u @= 0 ==> hcmod(x + u) - hcmod x \<in> Infinitesimal"
apply (drule approx_approx_zero_iff [THEN iffD1])
apply (rule_tac e = "hcmod u" and e' = "- hcmod u" in Infinitesimal_interval2)
apply (auto simp add: mem_infmal_iff [symmetric] diff_minus)
apply (rule_tac c1 = "hcmod x" in add_le_cancel_left [THEN iffD1])
apply (auto simp add: diff_minus [symmetric])
done

lemma approx_hcmod_add_hcmod: "u @= 0 ==> hcmod(x + u) @= hcmod x"
apply (rule approx_minus_iff [THEN iffD2])
apply (auto intro: Infinitesimal_hcmod_add_diff simp add: mem_infmal_iff [symmetric] diff_minus [symmetric])
done


subsection{*Zero is the Only Infinitesimal Complex Number*}

lemma Infinitesimal_less_SComplex:
   "[| x \<in> SComplex; y \<in> Infinitesimal; 0 < hcmod x |] ==> hcmod y < hcmod x"
by (auto intro: Infinitesimal_less_SReal SComplex_hcmod_SReal simp add: Infinitesimal_hcmod_iff)

lemma SComplex_Int_Infinitesimal_zero: "SComplex Int Infinitesimal = {0}"
by (auto simp add: Standard_def Infinitesimal_hcmod_iff)

lemma SComplex_Infinitesimal_zero:
     "[| x \<in> SComplex; x \<in> Infinitesimal|] ==> x = 0"
by (cut_tac SComplex_Int_Infinitesimal_zero, blast)

lemma SComplex_HFinite_diff_Infinitesimal:
     "[| x \<in> SComplex; x \<noteq> 0 |] ==> x \<in> HFinite - Infinitesimal"
by (auto dest: SComplex_Infinitesimal_zero Standard_subset_HFinite [THEN subsetD])

lemma hcomplex_of_complex_HFinite_diff_Infinitesimal:
     "hcomplex_of_complex x \<noteq> 0 
      ==> hcomplex_of_complex x \<in> HFinite - Infinitesimal"
by (rule SComplex_HFinite_diff_Infinitesimal, auto)

lemma numeral_not_Infinitesimal [simp]:
     "numeral w \<noteq> (0::hcomplex) ==> (numeral w::hcomplex) \<notin> Infinitesimal"
by (fast dest: Standard_numeral [THEN SComplex_Infinitesimal_zero])

lemma approx_SComplex_not_zero:
     "[| y \<in> SComplex; x @= y; y\<noteq> 0 |] ==> x \<noteq> 0"
by (auto dest: SComplex_Infinitesimal_zero approx_sym [THEN mem_infmal_iff [THEN iffD2]])

lemma SComplex_approx_iff:
     "[|x \<in> SComplex; y \<in> SComplex|] ==> (x @= y) = (x = y)"
by (auto simp add: Standard_def)

lemma numeral_Infinitesimal_iff [simp]:
     "((numeral w :: hcomplex) \<in> Infinitesimal) =
      (numeral w = (0::hcomplex))"
apply (rule iffI)
apply (fast dest: Standard_numeral [THEN SComplex_Infinitesimal_zero])
apply (simp (no_asm_simp))
done

lemma approx_unique_complex:
     "[| r \<in> SComplex; s \<in> SComplex; r @= x; s @= x|] ==> r = s"
by (blast intro: SComplex_approx_iff [THEN iffD1] approx_trans2)

subsection {* Properties of @{term hRe}, @{term hIm} and @{term HComplex} *}


lemma abs_hRe_le_hcmod: "\<And>x. \<bar>hRe x\<bar> \<le> hcmod x"
by transfer (rule abs_Re_le_cmod)

lemma abs_hIm_le_hcmod: "\<And>x. \<bar>hIm x\<bar> \<le> hcmod x"
by transfer (rule abs_Im_le_cmod)

lemma Infinitesimal_hRe: "x \<in> Infinitesimal \<Longrightarrow> hRe x \<in> Infinitesimal"
apply (rule InfinitesimalI2, simp)
apply (rule order_le_less_trans [OF abs_hRe_le_hcmod])
apply (erule (1) InfinitesimalD2)
done

lemma Infinitesimal_hIm: "x \<in> Infinitesimal \<Longrightarrow> hIm x \<in> Infinitesimal"
apply (rule InfinitesimalI2, simp)
apply (rule order_le_less_trans [OF abs_hIm_le_hcmod])
apply (erule (1) InfinitesimalD2)
done

lemma real_sqrt_lessI: "\<lbrakk>0 < u; x < u\<twosuperior>\<rbrakk> \<Longrightarrow> sqrt x < u"
(* TODO: this belongs somewhere else *)
by (frule real_sqrt_less_mono) simp

lemma hypreal_sqrt_lessI:
  "\<And>x u. \<lbrakk>0 < u; x < u\<twosuperior>\<rbrakk> \<Longrightarrow> ( *f* sqrt) x < u"
by transfer (rule real_sqrt_lessI)
 
lemma hypreal_sqrt_ge_zero: "\<And>x. 0 \<le> x \<Longrightarrow> 0 \<le> ( *f* sqrt) x"
by transfer (rule real_sqrt_ge_zero)

lemma Infinitesimal_sqrt:
  "\<lbrakk>x \<in> Infinitesimal; 0 \<le> x\<rbrakk> \<Longrightarrow> ( *f* sqrt) x \<in> Infinitesimal"
apply (rule InfinitesimalI2)
apply (drule_tac r="r\<twosuperior>" in InfinitesimalD2, simp)
apply (simp add: hypreal_sqrt_ge_zero)
apply (rule hypreal_sqrt_lessI, simp_all)
done

lemma Infinitesimal_HComplex:
  "\<lbrakk>x \<in> Infinitesimal; y \<in> Infinitesimal\<rbrakk> \<Longrightarrow> HComplex x y \<in> Infinitesimal"
apply (rule Infinitesimal_hcmod_iff [THEN iffD2])
apply (simp add: hcmod_i)
apply (rule Infinitesimal_add)
apply (erule Infinitesimal_hrealpow, simp)
apply (erule Infinitesimal_hrealpow, simp)
done

lemma hcomplex_Infinitesimal_iff:
  "(x \<in> Infinitesimal) = (hRe x \<in> Infinitesimal \<and> hIm x \<in> Infinitesimal)"
apply (safe intro!: Infinitesimal_hRe Infinitesimal_hIm)
apply (drule (1) Infinitesimal_HComplex, simp)
done

lemma hRe_diff [simp]: "\<And>x y. hRe (x - y) = hRe x - hRe y"
by transfer (rule complex_Re_diff)

lemma hIm_diff [simp]: "\<And>x y. hIm (x - y) = hIm x - hIm y"
by transfer (rule complex_Im_diff)

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
apply (auto simp add: HFinite_def SReal_def)
apply (rule_tac x="star_of r" in exI, simp)
apply (erule order_le_less_trans [OF abs_hRe_le_hcmod])
done

lemma HFinite_hIm: "x \<in> HFinite \<Longrightarrow> hIm x \<in> HFinite"
apply (auto simp add: HFinite_def SReal_def)
apply (rule_tac x="star_of r" in exI, simp)
apply (erule order_le_less_trans [OF abs_hIm_le_hcmod])
done

lemma HFinite_HComplex:
  "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> HComplex x y \<in> HFinite"
apply (subgoal_tac "HComplex x 0 + HComplex 0 y \<in> HFinite", simp)
apply (rule HFinite_add)
apply (simp add: HFinite_hcmod_iff hcmod_i)
apply (simp add: HFinite_hcmod_iff hcmod_i)
done

lemma hcomplex_HFinite_iff:
  "(x \<in> HFinite) = (hRe x \<in> HFinite \<and> hIm x \<in> HFinite)"
apply (safe intro!: HFinite_hRe HFinite_hIm)
apply (drule (1) HFinite_HComplex, simp)
done

lemma hcomplex_HInfinite_iff:
  "(x \<in> HInfinite) = (hRe x \<in> HInfinite \<or> hIm x \<in> HInfinite)"
by (simp add: HInfinite_HFinite_iff hcomplex_HFinite_iff)

lemma hcomplex_of_hypreal_approx_iff [simp]:
     "(hcomplex_of_hypreal x @= hcomplex_of_hypreal z) = (x @= z)"
by (simp add: hcomplex_approx_iff)

lemma Standard_HComplex:
  "\<lbrakk>x \<in> Standard; y \<in> Standard\<rbrakk> \<Longrightarrow> HComplex x y \<in> Standard"
by (simp add: HComplex_def)

(* Here we go - easy proof now!! *)
lemma stc_part_Ex: "x:HFinite ==> \<exists>t \<in> SComplex. x @= t"
apply (simp add: hcomplex_HFinite_iff hcomplex_approx_iff)
apply (rule_tac x="HComplex (st (hRe x)) (st (hIm x))" in bexI)
apply (simp add: st_approx_self [THEN approx_sym])
apply (simp add: Standard_HComplex st_SReal [unfolded Reals_eq_Standard])
done

lemma stc_part_Ex1: "x:HFinite ==> EX! t. t \<in> SComplex &  x @= t"
apply (drule stc_part_Ex, safe)
apply (drule_tac [2] approx_sym, drule_tac [2] approx_sym, drule_tac [2] approx_sym)
apply (auto intro!: approx_unique_complex)
done

lemmas hcomplex_of_complex_approx_inverse =
  hcomplex_of_complex_HFinite_diff_Infinitesimal [THEN [2] approx_inverse]


subsection{*Theorems About Monads*}

lemma monad_zero_hcmod_iff: "(x \<in> monad 0) = (hcmod x:monad 0)"
by (simp add: Infinitesimal_monad_zero_iff [symmetric] Infinitesimal_hcmod_iff)


subsection{*Theorems About Standard Part*}

lemma stc_approx_self: "x \<in> HFinite ==> stc x @= x"
apply (simp add: stc_def)
apply (frule stc_part_Ex, safe)
apply (rule someI2)
apply (auto intro: approx_sym)
done

lemma stc_SComplex: "x \<in> HFinite ==> stc x \<in> SComplex"
apply (simp add: stc_def)
apply (frule stc_part_Ex, safe)
apply (rule someI2)
apply (auto intro: approx_sym)
done

lemma stc_HFinite: "x \<in> HFinite ==> stc x \<in> HFinite"
by (erule stc_SComplex [THEN Standard_subset_HFinite [THEN subsetD]])

lemma stc_unique: "\<lbrakk>y \<in> SComplex; y \<approx> x\<rbrakk> \<Longrightarrow> stc x = y"
apply (frule Standard_subset_HFinite [THEN subsetD])
apply (drule (1) approx_HFinite)
apply (unfold stc_def)
apply (rule some_equality)
apply (auto intro: approx_unique_complex)
done

lemma stc_SComplex_eq [simp]: "x \<in> SComplex ==> stc x = x"
apply (erule stc_unique)
apply (rule approx_refl)
done

lemma stc_hcomplex_of_complex:
     "stc (hcomplex_of_complex x) = hcomplex_of_complex x"
by auto

lemma stc_eq_approx:
     "[| x \<in> HFinite; y \<in> HFinite; stc x = stc y |] ==> x @= y"
by (auto dest!: stc_approx_self elim!: approx_trans3)

lemma approx_stc_eq:
     "[| x \<in> HFinite; y \<in> HFinite; x @= y |] ==> stc x = stc y"
by (blast intro: approx_trans approx_trans2 SComplex_approx_iff [THEN iffD1]
          dest: stc_approx_self stc_SComplex)

lemma stc_eq_approx_iff:
     "[| x \<in> HFinite; y \<in> HFinite|] ==> (x @= y) = (stc x = stc y)"
by (blast intro: approx_stc_eq stc_eq_approx)

lemma stc_Infinitesimal_add_SComplex:
     "[| x \<in> SComplex; e \<in> Infinitesimal |] ==> stc(x + e) = x"
apply (erule stc_unique)
apply (erule Infinitesimal_add_approx_self)
done

lemma stc_Infinitesimal_add_SComplex2:
     "[| x \<in> SComplex; e \<in> Infinitesimal |] ==> stc(e + x) = x"
apply (erule stc_unique)
apply (erule Infinitesimal_add_approx_self2)
done

lemma HFinite_stc_Infinitesimal_add:
     "x \<in> HFinite ==> \<exists>e \<in> Infinitesimal. x = stc(x) + e"
by (blast dest!: stc_approx_self [THEN approx_sym] bex_Infinitesimal_iff2 [THEN iffD2])

lemma stc_add:
     "[| x \<in> HFinite; y \<in> HFinite |] ==> stc (x + y) = stc(x) + stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_add)

lemma stc_numeral [simp]: "stc (numeral w) = numeral w"
by (rule Standard_numeral [THEN stc_SComplex_eq])

lemma stc_zero [simp]: "stc 0 = 0"
by simp

lemma stc_one [simp]: "stc 1 = 1"
by simp

lemma stc_minus: "y \<in> HFinite ==> stc(-y) = -stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_minus)

lemma stc_diff: 
     "[| x \<in> HFinite; y \<in> HFinite |] ==> stc (x-y) = stc(x) - stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_diff)

lemma stc_mult:
     "[| x \<in> HFinite; y \<in> HFinite |]  
               ==> stc (x * y) = stc(x) * stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_mult_HFinite)

lemma stc_Infinitesimal: "x \<in> Infinitesimal ==> stc x = 0"
by (simp add: stc_unique mem_infmal_iff)

lemma stc_not_Infinitesimal: "stc(x) \<noteq> 0 ==> x \<notin> Infinitesimal"
by (fast intro: stc_Infinitesimal)

lemma stc_inverse:
     "[| x \<in> HFinite; stc x \<noteq> 0 |]  
      ==> stc(inverse x) = inverse (stc x)"
apply (drule stc_not_Infinitesimal)
apply (simp add: stc_unique stc_SComplex stc_approx_self approx_inverse)
done

lemma stc_divide [simp]:
     "[| x \<in> HFinite; y \<in> HFinite; stc y \<noteq> 0 |]  
      ==> stc(x/y) = (stc x) / (stc y)"
by (simp add: divide_inverse stc_mult stc_not_Infinitesimal HFinite_inverse stc_inverse)

lemma stc_idempotent [simp]: "x \<in> HFinite ==> stc(stc(x)) = stc(x)"
by (blast intro: stc_HFinite stc_approx_self approx_stc_eq)

lemma HFinite_HFinite_hcomplex_of_hypreal:
     "z \<in> HFinite ==> hcomplex_of_hypreal z \<in> HFinite"
by (simp add: hcomplex_HFinite_iff)

lemma SComplex_SReal_hcomplex_of_hypreal:
     "x \<in> Reals ==>  hcomplex_of_hypreal x \<in> SComplex"
apply (rule Standard_of_hypreal)
apply (simp add: Reals_eq_Standard)
done

lemma stc_hcomplex_of_hypreal: 
 "z \<in> HFinite ==> stc(hcomplex_of_hypreal z) = hcomplex_of_hypreal (st z)"
apply (rule stc_unique)
apply (rule SComplex_SReal_hcomplex_of_hypreal)
apply (erule st_SReal)
apply (simp add: hcomplex_of_hypreal_approx_iff st_approx_self)
done

(*
Goal "x \<in> HFinite ==> hcmod(stc x) = st(hcmod x)"
by (dtac stc_approx_self 1)
by (auto_tac (claset(),simpset() addsimps [bex_Infinitesimal_iff2 RS sym]));


approx_hcmod_add_hcmod
*)

lemma Infinitesimal_hcnj_iff [simp]:
     "(hcnj z \<in> Infinitesimal) = (z \<in> Infinitesimal)"
by (simp add: Infinitesimal_hcmod_iff)

lemma Infinitesimal_hcomplex_of_hypreal_epsilon [simp]:
     "hcomplex_of_hypreal epsilon \<in> Infinitesimal"
by (simp add: Infinitesimal_hcmod_iff)

end

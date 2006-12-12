(*  Title       : NSCA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001,2002 University of Edinburgh
*)

header{*Non-Standard Complex Analysis*}

theory NSCA
imports NSComplex
begin

definition
   (* standard complex numbers reagarded as an embedded subset of NS complex *)
   SComplex  :: "hcomplex set" where
   "SComplex = {x. \<exists>r. x = hcomplex_of_complex r}"

definition
   stc :: "hcomplex => hcomplex" where
    --{* standard part map*}
   "stc x = (SOME r. x \<in> HFinite & r:SComplex & r @= x)"


subsection{*Closure Laws for SComplex, the Standard Complex Numbers*}

lemma SComplex_add: "[| x \<in> SComplex; y \<in> SComplex |] ==> x + y \<in> SComplex"
apply (simp add: SComplex_def, safe)
apply (rule_tac x = "r + ra" in exI, simp)
done

lemma SComplex_mult: "[| x \<in> SComplex; y \<in> SComplex |] ==> x * y \<in> SComplex"
apply (simp add: SComplex_def, safe)
apply (rule_tac x = "r * ra" in exI, simp)
done

lemma SComplex_inverse: "x \<in> SComplex ==> inverse x \<in> SComplex"
apply (simp add: SComplex_def)
apply (blast intro: star_of_inverse [symmetric])
done

lemma SComplex_divide: "[| x \<in> SComplex;  y \<in> SComplex |] ==> x/y \<in> SComplex"
by (simp add: SComplex_mult SComplex_inverse divide_inverse)

lemma SComplex_minus: "x \<in> SComplex ==> -x \<in> SComplex"
apply (simp add: SComplex_def)
apply (blast intro: star_of_minus [symmetric])
done

lemma SComplex_minus_iff [simp]: "(-x \<in> SComplex) = (x \<in> SComplex)"
apply auto
apply (erule_tac [2] SComplex_minus)
apply (drule SComplex_minus, auto)
done

lemma SComplex_diff: "[| x \<in> SComplex; y \<in> SComplex |] ==> x - y \<in> SComplex"
by (simp add: diff_minus SComplex_add) 

lemma SComplex_add_cancel:
     "[| x + y \<in> SComplex; y \<in> SComplex |] ==> x \<in> SComplex"
by (drule SComplex_diff, assumption, simp)

lemma SReal_hcmod_hcomplex_of_complex [simp]:
     "hcmod (hcomplex_of_complex r) \<in> Reals"
by (auto simp add: hcmod SReal_def star_of_def)

lemma SReal_hcmod_number_of [simp]: "hcmod (number_of w ::hcomplex) \<in> Reals"
apply (subst star_of_number_of [symmetric])
apply (rule SReal_hcmod_hcomplex_of_complex)
done

lemma SReal_hcmod_SComplex: "x \<in> SComplex ==> hcmod x \<in> Reals"
by (auto simp add: SComplex_def)

lemma SComplex_hcomplex_of_complex [simp]: "hcomplex_of_complex x \<in> SComplex"
by (simp add: SComplex_def)

lemma SComplex_number_of [simp]: "(number_of w ::hcomplex) \<in> SComplex"
apply (subst star_of_number_of [symmetric])
apply (rule SComplex_hcomplex_of_complex)
done

lemma SComplex_divide_number_of:
     "r \<in> SComplex ==> r/(number_of w::hcomplex) \<in> SComplex"
apply (simp only: divide_inverse)
apply (blast intro!: SComplex_number_of SComplex_mult SComplex_inverse)
done

lemma SComplex_UNIV_complex:
     "{x. hcomplex_of_complex x \<in> SComplex} = (UNIV::complex set)"
by (simp add: SComplex_def)

lemma SComplex_iff: "(x \<in> SComplex) = (\<exists>y. x = hcomplex_of_complex y)"
by (simp add: SComplex_def)

lemma hcomplex_of_complex_image:
     "hcomplex_of_complex `(UNIV::complex set) = SComplex"
by (auto simp add: SComplex_def)

lemma inv_hcomplex_of_complex_image: "inv hcomplex_of_complex `SComplex = UNIV"
apply (auto simp add: SComplex_def)
apply (rule inj_hcomplex_of_complex [THEN inv_f_f, THEN subst], blast)
done

lemma SComplex_hcomplex_of_complex_image: 
      "[| \<exists>x. x: P; P \<le> SComplex |] ==> \<exists>Q. P = hcomplex_of_complex ` Q"
apply (simp add: SComplex_def, blast)
done

lemma SComplex_SReal_dense:
     "[| x \<in> SComplex; y \<in> SComplex; hcmod x < hcmod y  
      |] ==> \<exists>r \<in> Reals. hcmod x< r & r < hcmod y"
apply (auto intro: SReal_dense simp add: SReal_hcmod_SComplex)
done

lemma SComplex_hcmod_SReal: 
      "z \<in> SComplex ==> hcmod z \<in> Reals"
by (auto simp add: SComplex_def)

lemma SComplex_zero [simp]: "0 \<in> SComplex"
by (simp add: SComplex_def)

lemma SComplex_one [simp]: "1 \<in> SComplex"
by (simp add: SComplex_def)

(*
Goalw [SComplex_def,SReal_def] "hcmod z \<in> Reals ==> z \<in> SComplex"
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hypreal_of_real_def,
    hcomplex_of_complex_def,cmod_def]));
*)


subsection{*The Finite Elements form a Subring*}

lemma SComplex_subset_HFinite [simp]: "SComplex \<le> HFinite"
by (auto simp add: SComplex_def)

lemma HFinite_hcmod_hcomplex_of_complex [simp]:
     "hcmod (hcomplex_of_complex r) \<in> HFinite"
by (auto intro!: SReal_subset_HFinite [THEN subsetD])

lemma HFinite_hcomplex_of_complex: "hcomplex_of_complex x \<in> HFinite"
by (rule HFinite_star_of)

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

lemma approx_mult_subst_SComplex:
     "[| u @= x*hcomplex_of_complex v; x @= y |] 
      ==> u @= y*hcomplex_of_complex v"
by (rule approx_mult_subst_star_of)

lemma approx_hcomplex_of_complex_HFinite:
     "x @= hcomplex_of_complex D ==> x \<in> HFinite"
by (rule approx_star_of_HFinite)

lemma approx_mult_hcomplex_of_complex:
     "[|a @= hcomplex_of_complex b; c @= hcomplex_of_complex d |]  
      ==> a*c @= hcomplex_of_complex b * hcomplex_of_complex d"
by (rule approx_mult_star_of)

lemma approx_SComplex_mult_cancel_zero:
     "[| a \<in> SComplex; a \<noteq> 0; a*x @= 0 |] ==> x @= 0"
apply (drule SComplex_inverse [THEN SComplex_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_mult_SComplex1: "[| a \<in> SComplex; x @= 0 |] ==> x*a @= 0"
by (auto dest: SComplex_subset_HFinite [THEN subsetD] approx_mult1)

lemma approx_mult_SComplex2: "[| a \<in> SComplex; x @= 0 |] ==> a*x @= 0"
by (auto dest: SComplex_subset_HFinite [THEN subsetD] approx_mult2)

lemma approx_mult_SComplex_zero_cancel_iff [simp]:
     "[|a \<in> SComplex; a \<noteq> 0 |] ==> (a*x @= 0) = (x @= 0)"
by (blast intro: approx_SComplex_mult_cancel_zero approx_mult_SComplex2)

lemma approx_SComplex_mult_cancel:
     "[| a \<in> SComplex; a \<noteq> 0; a* w @= a*z |] ==> w @= z"
apply (drule SComplex_inverse [THEN SComplex_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: mult_assoc [symmetric])
done

lemma approx_SComplex_mult_cancel_iff1 [simp]:
     "[| a \<in> SComplex; a \<noteq> 0|] ==> (a* w @= a*z) = (w @= z)"
by (auto intro!: approx_mult2 SComplex_subset_HFinite [THEN subsetD]
            intro: approx_SComplex_mult_cancel)

(* TODO: generalize following theorems: hcmod -> hnorm *)

lemma approx_hcmod_approx_zero: "(x @= y) = (hcmod (y - x) @= 0)"
apply (subst hcmod_diff_commute)
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
apply (auto simp add: mem_infmal_iff [symmetric] diff_def)
apply (rule_tac c1 = "hcmod x" in add_le_cancel_left [THEN iffD1])
apply (auto simp add: diff_minus [symmetric])
done

lemma approx_hcmod_add_hcmod: "u @= 0 ==> hcmod(x + u) @= hcmod x"
apply (rule approx_minus_iff [THEN iffD2])
apply (auto intro: Infinitesimal_hcmod_add_diff simp add: mem_infmal_iff [symmetric] diff_minus [symmetric])
done

lemma approx_hcmod_approx: "x @= y ==> hcmod x @= hcmod y"
by (rule approx_hnorm)


subsection{*Zero is the Only Infinitesimal Complex Number*}

lemma Infinitesimal_less_SComplex:
   "[| x \<in> SComplex; y \<in> Infinitesimal; 0 < hcmod x |] ==> hcmod y < hcmod x"
by (auto intro: Infinitesimal_less_SReal SComplex_hcmod_SReal simp add: Infinitesimal_hcmod_iff)

lemma SComplex_Int_Infinitesimal_zero: "SComplex Int Infinitesimal = {0}"
by (auto simp add: SComplex_def Infinitesimal_hcmod_iff)

lemma SComplex_Infinitesimal_zero:
     "[| x \<in> SComplex; x \<in> Infinitesimal|] ==> x = 0"
by (cut_tac SComplex_Int_Infinitesimal_zero, blast)

lemma SComplex_HFinite_diff_Infinitesimal:
     "[| x \<in> SComplex; x \<noteq> 0 |] ==> x \<in> HFinite - Infinitesimal"
by (auto dest: SComplex_Infinitesimal_zero SComplex_subset_HFinite [THEN subsetD])

lemma hcomplex_of_complex_HFinite_diff_Infinitesimal:
     "hcomplex_of_complex x \<noteq> 0 
      ==> hcomplex_of_complex x \<in> HFinite - Infinitesimal"
by (rule SComplex_HFinite_diff_Infinitesimal, auto)

lemma hcomplex_of_complex_Infinitesimal_iff_0:
     "(hcomplex_of_complex x \<in> Infinitesimal) = (x=0)"
by (rule star_of_Infinitesimal_iff_0)

lemma number_of_not_Infinitesimal [simp]:
     "number_of w \<noteq> (0::hcomplex) ==> (number_of w::hcomplex) \<notin> Infinitesimal"
by (fast dest: SComplex_number_of [THEN SComplex_Infinitesimal_zero])

lemma approx_SComplex_not_zero:
     "[| y \<in> SComplex; x @= y; y\<noteq> 0 |] ==> x \<noteq> 0"
by (auto dest: SComplex_Infinitesimal_zero approx_sym [THEN mem_infmal_iff [THEN iffD2]])

lemma SComplex_approx_iff:
     "[|x \<in> SComplex; y \<in> SComplex|] ==> (x @= y) = (x = y)"
by (auto simp add: SComplex_def)

lemma number_of_Infinitesimal_iff [simp]:
     "((number_of w :: hcomplex) \<in> Infinitesimal) =
      (number_of w = (0::hcomplex))"
apply (rule iffI)
apply (fast dest: SComplex_number_of [THEN SComplex_Infinitesimal_zero])
apply (simp (no_asm_simp))
done

lemma hcomplex_of_complex_approx_iff:
     "(hcomplex_of_complex k @= hcomplex_of_complex m) = (k = m)"
by (rule star_of_approx_iff)

lemma hcomplex_of_complex_approx_number_of_iff [simp]:
     "(hcomplex_of_complex k @= number_of w) = (k = number_of w)"
by (subst hcomplex_of_complex_approx_iff [symmetric], auto)

lemma approx_unique_complex:
     "[| r \<in> SComplex; s \<in> SComplex; r @= x; s @= x|] ==> r = s"
by (blast intro: SComplex_approx_iff [THEN iffD1] approx_trans2)

lemma hcomplex_approxD1:
     "star_n X @= star_n Y
      ==> star_n (%n. Re(X n)) @= star_n (%n. Re(Y n))"
apply (simp (no_asm) add: approx_FreeUltrafilterNat_iff2, safe)
apply (drule approx_minus_iff [THEN iffD1])
apply (simp add: star_n_diff mem_infmal_iff [symmetric] Infinitesimal_hcmod_iff hcmod Infinitesimal_FreeUltrafilterNat_iff2)
apply (drule_tac x = m in spec)
apply (erule ultra, rule FreeUltrafilterNat_all, clarify)
apply (rule_tac y="cmod (X n - Y n)" in order_le_less_trans)
apply (case_tac "X n")
apply (case_tac "Y n")
apply (auto simp add: complex_diff complex_mod
            simp del: realpow_Suc)
done

(* same proof *)
lemma hcomplex_approxD2:
     "star_n X @= star_n Y
      ==> star_n (%n. Im(X n)) @= star_n (%n. Im(Y n))"
apply (simp (no_asm) add: approx_FreeUltrafilterNat_iff2, safe)
apply (drule approx_minus_iff [THEN iffD1])
apply (simp add: star_n_diff mem_infmal_iff [symmetric] Infinitesimal_hcmod_iff hcmod Infinitesimal_FreeUltrafilterNat_iff2)
apply (drule_tac x = m in spec)
apply (erule ultra, rule FreeUltrafilterNat_all, clarify)
apply (rule_tac y="cmod (X n - Y n)" in order_le_less_trans)
apply (case_tac "X n")
apply (case_tac "Y n")
apply (auto simp add: complex_diff complex_mod
            simp del: realpow_Suc)
done

lemma hcomplex_approxI:
     "[| star_n (%n. Re(X n)) @= star_n (%n. Re(Y n));  
         star_n (%n. Im(X n)) @= star_n (%n. Im(Y n))  
      |] ==> star_n X @= star_n Y"
apply (drule approx_minus_iff [THEN iffD1])
apply (drule approx_minus_iff [THEN iffD1])
apply (rule approx_minus_iff [THEN iffD2])
apply (auto simp add: mem_infmal_iff [symmetric] mem_infmal_iff [symmetric] star_n_diff Infinitesimal_hcmod_iff hcmod Infinitesimal_FreeUltrafilterNat_iff)
apply (drule_tac x = "u/2" in spec)
apply (drule_tac x = "u/2" in spec, auto, ultra)
apply (case_tac "X x")
apply (case_tac "Y x")
apply (auto simp add: complex_diff complex_mod snd_conv fst_conv numeral_2_eq_2)
apply (rename_tac a b c d)
apply (subgoal_tac "sqrt (abs (a - c) ^ 2 + abs (b - d) ^ 2) < u")
apply (rule_tac [2] lemma_sqrt_hcomplex_capprox, auto)
apply (simp add: power2_eq_square)
done

lemma approx_approx_iff:
     "(star_n X @= star_n Y) = 
       (star_n (%n. Re(X n)) @= star_n (%n. Re(Y n)) &  
        star_n (%n. Im(X n)) @= star_n (%n. Im(Y n)))"
apply (blast intro: hcomplex_approxI hcomplex_approxD1 hcomplex_approxD2)
done

lemma hcomplex_of_hypreal_approx_iff [simp]:
     "(hcomplex_of_hypreal x @= hcomplex_of_hypreal z) = (x @= z)"
apply (cases x, cases z)
apply (simp add: hcomplex_of_hypreal approx_approx_iff)
done

lemma HFinite_HFinite_Re:
     "star_n X \<in> HFinite  
      ==> star_n (%n. Re(X n)) \<in> HFinite"
apply (auto simp add: HFinite_hcmod_iff hcmod HFinite_FreeUltrafilterNat_iff)
apply (rule_tac x = u in exI, ultra)
apply (case_tac "X x")
apply (auto simp add: complex_mod numeral_2_eq_2 simp del: realpow_Suc)
apply (rule ccontr, drule linorder_not_less [THEN iffD1])
apply (drule order_less_le_trans, assumption)
apply (drule real_sqrt_ge_abs1 [THEN [2] order_less_le_trans]) 
apply (auto simp add: numeral_2_eq_2 [symmetric]) 
done

lemma HFinite_HFinite_Im:
     "star_n X \<in> HFinite  
      ==> star_n (%n. Im(X n)) \<in> HFinite"
apply (auto simp add: HFinite_hcmod_iff hcmod HFinite_FreeUltrafilterNat_iff)
apply (rule_tac x = u in exI, ultra)
apply (case_tac "X x")
apply (auto simp add: complex_mod simp del: realpow_Suc)
apply (rule ccontr, drule linorder_not_less [THEN iffD1])
apply (drule order_less_le_trans, assumption)
apply (drule real_sqrt_ge_abs2 [THEN [2] order_less_le_trans], auto) 
done

lemma HFinite_Re_Im_HFinite:
     "[| star_n (%n. Re(X n)) \<in> HFinite;  
         star_n (%n. Im(X n)) \<in> HFinite  
      |] ==> star_n X \<in> HFinite"
apply (auto simp add: HFinite_hcmod_iff hcmod HFinite_FreeUltrafilterNat_iff)
apply (rename_tac u v)
apply (rule_tac x = "2* (u + v) " in exI)
apply ultra
apply (case_tac "X x")
apply (auto simp add: complex_mod numeral_2_eq_2 simp del: realpow_Suc)
apply (subgoal_tac "0 < u")
 prefer 2 apply arith
apply (subgoal_tac "0 < v")
 prefer 2 apply arith
apply (subgoal_tac "sqrt (abs (Re (X x)) ^ 2 + abs (Im (X x)) ^ 2) < 2*u + 2*v")
apply (rule_tac [2] lemma_sqrt_hcomplex_capprox, auto)
apply (simp add: power2_eq_square)
done

lemma HFinite_HFinite_iff:
     "(star_n X \<in> HFinite) =  
      (star_n (%n. Re(X n)) \<in> HFinite &  
       star_n (%n. Im(X n)) \<in> HFinite)"
by (blast intro: HFinite_Re_Im_HFinite HFinite_HFinite_Im HFinite_HFinite_Re)

lemma SComplex_Re_SReal:
     "star_n X \<in> SComplex  
      ==> star_n (%n. Re(X n)) \<in> Reals"
apply (auto simp add: SComplex_def SReal_def star_of_def star_n_eq_iff)
apply (rule_tac x = "Re r" in exI, ultra)
done

lemma SComplex_Im_SReal:
     "star_n X \<in> SComplex  
      ==> star_n (%n. Im(X n)) \<in> Reals"
apply (auto simp add: SComplex_def SReal_def star_of_def star_n_eq_iff)
apply (rule_tac x = "Im r" in exI, ultra)
done

lemma Reals_Re_Im_SComplex:
     "[| star_n (%n. Re(X n)) \<in> Reals;  
         star_n (%n. Im(X n)) \<in> Reals  
      |] ==> star_n X \<in> SComplex"
apply (auto simp add: SComplex_def SReal_def star_of_def star_n_eq_iff)
apply (rule_tac x = "Complex r ra" in exI, ultra)
done

lemma SComplex_SReal_iff:
     "(star_n X \<in> SComplex) =  
      (star_n (%n. Re(X n)) \<in> Reals &  
       star_n (%n. Im(X n)) \<in> Reals)"
by (blast intro: SComplex_Re_SReal SComplex_Im_SReal Reals_Re_Im_SComplex)

lemma Infinitesimal_Infinitesimal_iff:
     "(star_n X \<in> Infinitesimal) =  
      (star_n (%n. Re(X n)) \<in> Infinitesimal &  
       star_n (%n. Im(X n)) \<in> Infinitesimal)"
by (simp add: mem_infmal_iff star_n_zero_num approx_approx_iff)

lemma eq_Abs_star_EX:
     "(\<exists>t. P t) = (\<exists>X. P (star_n X))"
by (rule ex_star_eq)

lemma eq_Abs_star_Bex:
     "(\<exists>t \<in> A. P t) = (\<exists>X. star_n X \<in> A & P (star_n X))"
by (simp add: Bex_def ex_star_eq)

(* Here we go - easy proof now!! *)
lemma stc_part_Ex: "x:HFinite ==> \<exists>t \<in> SComplex. x @= t"
apply (cases x)
apply (auto simp add: HFinite_HFinite_iff eq_Abs_star_Bex SComplex_SReal_iff approx_approx_iff)
apply (drule st_part_Ex, safe)+
apply (rule_tac x = t in star_cases)
apply (rule_tac x = ta in star_cases, auto)
apply (rule_tac x = "%n. Complex (Xa n) (Xb n) " in exI)
apply auto
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
by (erule stc_SComplex [THEN SComplex_subset_HFinite [THEN subsetD]])

lemma stc_unique: "\<lbrakk>y \<in> SComplex; y \<approx> x\<rbrakk> \<Longrightarrow> stc x = y"
apply (frule SComplex_subset_HFinite [THEN subsetD])
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
by (simp add: stc_unique stc_SComplex stc_approx_self approx_add SComplex_add)

lemma stc_number_of [simp]: "stc (number_of w) = number_of w"
by (rule SComplex_number_of [THEN stc_SComplex_eq])

lemma stc_zero [simp]: "stc 0 = 0"
by simp

lemma stc_one [simp]: "stc 1 = 1"
by simp

lemma stc_minus: "y \<in> HFinite ==> stc(-y) = -stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_minus)

lemma stc_diff: 
     "[| x \<in> HFinite; y \<in> HFinite |] ==> stc (x-y) = stc(x) - stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_diff SComplex_diff)

lemma stc_mult:
     "[| x \<in> HFinite; y \<in> HFinite |]  
               ==> stc (x * y) = stc(x) * stc(y)"
by (simp add: stc_unique stc_SComplex stc_approx_self approx_mult_HFinite SComplex_mult)

lemma stc_Infinitesimal: "x \<in> Infinitesimal ==> stc x = 0"
by (simp add: stc_unique mem_infmal_iff)

lemma stc_not_Infinitesimal: "stc(x) \<noteq> 0 ==> x \<notin> Infinitesimal"
by (fast intro: stc_Infinitesimal)

lemma stc_inverse:
     "[| x \<in> HFinite; stc x \<noteq> 0 |]  
      ==> stc(inverse x) = inverse (stc x)"
apply (drule stc_not_Infinitesimal)
apply (simp add: stc_unique stc_SComplex stc_approx_self approx_inverse SComplex_inverse)
done

lemma stc_divide [simp]:
     "[| x \<in> HFinite; y \<in> HFinite; stc y \<noteq> 0 |]  
      ==> stc(x/y) = (stc x) / (stc y)"
by (simp add: divide_inverse stc_mult stc_not_Infinitesimal HFinite_inverse stc_inverse)

lemma stc_idempotent [simp]: "x \<in> HFinite ==> stc(stc(x)) = stc(x)"
by (blast intro: stc_HFinite stc_approx_self approx_stc_eq)

lemma HFinite_HFinite_hcomplex_of_hypreal:
     "z \<in> HFinite ==> hcomplex_of_hypreal z \<in> HFinite"
apply (cases z)
apply (simp add: hcomplex_of_hypreal HFinite_HFinite_iff star_n_zero_num [symmetric])
done

lemma SComplex_SReal_hcomplex_of_hypreal:
     "x \<in> Reals ==>  hcomplex_of_hypreal x \<in> SComplex"
by (auto simp add: SReal_def Standard_def hcomplex_of_hypreal_def
         simp del: star_of_of_real)

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

lemma HInfinite_HInfinite_iff:
     "(star_n X \<in> HInfinite) =  
      (star_n (%n. Re(X n)) \<in> HInfinite |  
       star_n (%n. Im(X n)) \<in> HInfinite)"
by (simp add: HInfinite_HFinite_iff HFinite_HFinite_iff)

text{*These theorems should probably be deleted*}
lemma hcomplex_split_Infinitesimal_iff:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y \<in> Infinitesimal) =  
      (x \<in> Infinitesimal & y \<in> Infinitesimal)"
apply (cases x, cases y)
apply (simp add: iii_def star_of_def star_n_add star_n_mult hcomplex_of_hypreal Infinitesimal_Infinitesimal_iff)
done

lemma hcomplex_split_HFinite_iff:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y \<in> HFinite) =  
      (x \<in> HFinite & y \<in> HFinite)"
apply (cases x, cases y)
apply (simp add: iii_def star_of_def star_n_add star_n_mult hcomplex_of_hypreal HFinite_HFinite_iff)
done

lemma hcomplex_split_SComplex_iff:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y \<in> SComplex) =  
      (x \<in> Reals & y \<in> Reals)"
apply (cases x, cases y)
apply (simp add: iii_def star_of_def star_n_add star_n_mult hcomplex_of_hypreal SComplex_SReal_iff)
done

lemma hcomplex_split_HInfinite_iff:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y \<in> HInfinite) =  
      (x \<in> HInfinite | y \<in> HInfinite)"
apply (cases x, cases y)
apply (simp add: iii_def star_of_def star_n_add star_n_mult hcomplex_of_hypreal HInfinite_HInfinite_iff)
done

lemma hcomplex_split_approx_iff:
     "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y @=  
       hcomplex_of_hypreal x' + iii * hcomplex_of_hypreal y') =  
      (x @= x' & y @= y')"
apply (cases x, cases y, cases x', cases y')
apply (simp add: iii_def star_of_def star_n_add star_n_mult hcomplex_of_hypreal approx_approx_iff)
done

lemma complex_seq_to_hcomplex_Infinitesimal:
     "\<forall>n. cmod (X n - x) < inverse (real (Suc n)) ==>  
      star_n X - hcomplex_of_complex x \<in> Infinitesimal"
by (rule real_seq_to_hypreal_Infinitesimal [folded diff_def])

lemma Infinitesimal_hcomplex_of_hypreal_epsilon [simp]:
     "hcomplex_of_hypreal epsilon \<in> Infinitesimal"
by (simp add: Infinitesimal_hcmod_iff)

end

(*  Title       : NSA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
*)

header{*Infinite Numbers, Infinitesimals, Infinitely Close Relation*}

theory NSA = HyperArith + RComplete:

constdefs

  Infinitesimal  :: "hypreal set"
   "Infinitesimal == {x. \<forall>r \<in> Reals. 0 < r --> abs x < r}"

  HFinite :: "hypreal set"
   "HFinite == {x. \<exists>r \<in> Reals. abs x < r}"

  HInfinite :: "hypreal set"
   "HInfinite == {x. \<forall>r \<in> Reals. r < abs x}"

  (* standard part map *)
  st        :: "hypreal => hypreal"
   "st           == (%x. @r. x \<in> HFinite & r \<in> Reals & r @= x)"

  monad     :: "hypreal => hypreal set"
   "monad x      == {y. x @= y}"

  galaxy    :: "hypreal => hypreal set"
   "galaxy x     == {y. (x + -y) \<in> HFinite}"

  (* infinitely close *)
  approx :: "[hypreal, hypreal] => bool"    (infixl "@=" 50)
   "x @= y       == (x + -y) \<in> Infinitesimal"


defs (overloaded)

   (*standard real numbers as a subset of the hyperreals*)
   SReal_def:      "Reals == {x. \<exists>r. x = hypreal_of_real r}"

syntax (xsymbols)
    approx :: "[hypreal, hypreal] => bool"    (infixl "\<approx>" 50)



subsection{*Closure Laws for  Standard Reals*}

lemma SReal_add [simp]:
     "[| (x::hypreal) \<in> Reals; y \<in> Reals |] ==> x + y \<in> Reals"
apply (auto simp add: SReal_def)
apply (rule_tac x = "r + ra" in exI, simp)
done

lemma SReal_mult: "[| (x::hypreal) \<in> Reals; y \<in> Reals |] ==> x * y \<in> Reals"
apply (simp add: SReal_def, safe)
apply (rule_tac x = "r * ra" in exI)
apply (simp (no_asm) add: hypreal_of_real_mult)
done

lemma SReal_inverse: "(x::hypreal) \<in> Reals ==> inverse x \<in> Reals"
apply (simp add: SReal_def)
apply (blast intro: hypreal_of_real_inverse [symmetric])
done

lemma SReal_divide: "[| (x::hypreal) \<in> Reals;  y \<in> Reals |] ==> x/y \<in> Reals"
apply (simp (no_asm_simp) add: SReal_mult SReal_inverse hypreal_divide_def)
done

lemma SReal_minus: "(x::hypreal) \<in> Reals ==> -x \<in> Reals"
apply (simp add: SReal_def)
apply (blast intro: hypreal_of_real_minus [symmetric])
done

lemma SReal_minus_iff: "(-x \<in> Reals) = ((x::hypreal) \<in> Reals)"
apply auto
apply (erule_tac [2] SReal_minus)
apply (drule SReal_minus, auto)
done
declare SReal_minus_iff [simp]

lemma SReal_add_cancel:
     "[| (x::hypreal) + y \<in> Reals; y \<in> Reals |] ==> x \<in> Reals"
apply (drule_tac x = y in SReal_minus)
apply (drule SReal_add, assumption, auto)
done

lemma SReal_hrabs: "(x::hypreal) \<in> Reals ==> abs x \<in> Reals"
apply (simp add: SReal_def)
apply (auto simp add: hypreal_of_real_hrabs)
done

lemma SReal_hypreal_of_real: "hypreal_of_real x \<in> Reals"
by (simp add: SReal_def)
declare SReal_hypreal_of_real [simp]

lemma SReal_number_of: "(number_of w ::hypreal) \<in> Reals"
apply (simp only: hypreal_number_of [symmetric])
apply (rule SReal_hypreal_of_real)
done
declare SReal_number_of [simp]

(** As always with numerals, 0 and 1 are special cases **)

lemma Reals_0: "(0::hypreal) \<in> Reals"
apply (subst numeral_0_eq_0 [symmetric])
apply (rule SReal_number_of)
done
declare Reals_0 [simp]

lemma Reals_1: "(1::hypreal) \<in> Reals"
apply (subst numeral_1_eq_1 [symmetric])
apply (rule SReal_number_of)
done
declare Reals_1 [simp]

lemma SReal_divide_number_of: "r \<in> Reals ==> r/(number_of w::hypreal) \<in> Reals"
apply (unfold hypreal_divide_def)
apply (blast intro!: SReal_number_of SReal_mult SReal_inverse)
done

(* Infinitesimal epsilon not in Reals *)

lemma SReal_epsilon_not_mem: "epsilon \<notin> Reals"
apply (simp add: SReal_def)
apply (auto simp add: hypreal_of_real_not_eq_epsilon [THEN not_sym])
done

lemma SReal_omega_not_mem: "omega \<notin> Reals"
apply (simp add: SReal_def)
apply (auto simp add: hypreal_of_real_not_eq_omega [THEN not_sym])
done

lemma SReal_UNIV_real: "{x. hypreal_of_real x \<in> Reals} = (UNIV::real set)"
by (simp add: SReal_def)

lemma SReal_iff: "(x \<in> Reals) = (\<exists>y. x = hypreal_of_real y)"
by (simp add: SReal_def)

lemma hypreal_of_real_image: "hypreal_of_real `(UNIV::real set) = Reals"
by (auto simp add: SReal_def)

lemma inv_hypreal_of_real_image: "inv hypreal_of_real ` Reals = UNIV"
apply (auto simp add: SReal_def)
apply (rule inj_hypreal_of_real [THEN inv_f_f, THEN subst], blast)
done

lemma SReal_hypreal_of_real_image:
      "[| \<exists>x. x: P; P \<subseteq> Reals |] ==> \<exists>Q. P = hypreal_of_real ` Q"
apply (simp add: SReal_def, blast)
done

lemma SReal_dense:
     "[| (x::hypreal) \<in> Reals; y \<in> Reals;  x<y |] ==> \<exists>r \<in> Reals. x<r & r<y"
apply (auto simp add: SReal_iff)
apply (drule dense, safe)
apply (rule_tac x = "hypreal_of_real r" in bexI, auto)
done

(*------------------------------------------------------------------
                   Completeness of Reals
 ------------------------------------------------------------------*)
lemma SReal_sup_lemma:
     "P \<subseteq> Reals ==> ((\<exists>x \<in> P. y < x) =
      (\<exists>X. hypreal_of_real X \<in> P & y < hypreal_of_real X))"
by (blast dest!: SReal_iff [THEN iffD1])

lemma SReal_sup_lemma2:
     "[| P \<subseteq> Reals; \<exists>x. x \<in> P; \<exists>y \<in> Reals. \<forall>x \<in> P. x < y |]
      ==> (\<exists>X. X \<in> {w. hypreal_of_real w \<in> P}) &
          (\<exists>Y. \<forall>X \<in> {w. hypreal_of_real w \<in> P}. X < Y)"
apply (rule conjI)
apply (fast dest!: SReal_iff [THEN iffD1])
apply (auto, frule subsetD, assumption)
apply (drule SReal_iff [THEN iffD1])
apply (auto, rule_tac x = ya in exI, auto)
done

(*------------------------------------------------------
    lifting of ub and property of lub
 -------------------------------------------------------*)
lemma hypreal_of_real_isUb_iff:
      "(isUb (Reals) (hypreal_of_real ` Q) (hypreal_of_real Y)) =
       (isUb (UNIV :: real set) Q Y)"
apply (simp add: isUb_def setle_def)
done

lemma hypreal_of_real_isLub1:
     "isLub Reals (hypreal_of_real ` Q) (hypreal_of_real Y)
      ==> isLub (UNIV :: real set) Q Y"
apply (simp add: isLub_def leastP_def)
apply (auto intro: hypreal_of_real_isUb_iff [THEN iffD2]
            simp add: hypreal_of_real_isUb_iff setge_def)
done

lemma hypreal_of_real_isLub2:
      "isLub (UNIV :: real set) Q Y
       ==> isLub Reals (hypreal_of_real ` Q) (hypreal_of_real Y)"
apply (simp add: isLub_def leastP_def)
apply (auto simp add: hypreal_of_real_isUb_iff setge_def)
apply (frule_tac x2 = x in isUbD2a [THEN SReal_iff [THEN iffD1], THEN exE])
 prefer 2 apply assumption
apply (drule_tac x = xa in spec)
apply (auto simp add: hypreal_of_real_isUb_iff)
done

lemma hypreal_of_real_isLub_iff:
     "(isLub Reals (hypreal_of_real ` Q) (hypreal_of_real Y)) =
      (isLub (UNIV :: real set) Q Y)"
by (blast intro: hypreal_of_real_isLub1 hypreal_of_real_isLub2)

(* lemmas *)
lemma lemma_isUb_hypreal_of_real:
     "isUb Reals P Y ==> \<exists>Yo. isUb Reals P (hypreal_of_real Yo)"
by (auto simp add: SReal_iff isUb_def)

lemma lemma_isLub_hypreal_of_real:
     "isLub Reals P Y ==> \<exists>Yo. isLub Reals P (hypreal_of_real Yo)"
by (auto simp add: isLub_def leastP_def isUb_def SReal_iff)

lemma lemma_isLub_hypreal_of_real2:
     "\<exists>Yo. isLub Reals P (hypreal_of_real Yo) ==> \<exists>Y. isLub Reals P Y"
by (auto simp add: isLub_def leastP_def isUb_def)

lemma SReal_complete:
     "[| P \<subseteq> Reals;  \<exists>x. x \<in> P;  \<exists>Y. isUb Reals P Y |]
      ==> \<exists>t::hypreal. isLub Reals P t"
apply (frule SReal_hypreal_of_real_image)
apply (auto, drule lemma_isUb_hypreal_of_real)
apply (auto intro!: reals_complete lemma_isLub_hypreal_of_real2 simp add: hypreal_of_real_isLub_iff hypreal_of_real_isUb_iff)
done


subsection{* Set of Finite Elements is a Subring of the Extended Reals*}

lemma HFinite_add: "[|x \<in> HFinite; y \<in> HFinite|] ==> (x+y) \<in> HFinite"
apply (simp add: HFinite_def)
apply (blast intro!: SReal_add hrabs_add_less)
done

lemma HFinite_mult: "[|x \<in> HFinite; y \<in> HFinite|] ==> x*y \<in> HFinite"
apply (simp add: HFinite_def)
apply (blast intro!: SReal_mult abs_mult_less)
done

lemma HFinite_minus_iff: "(-x \<in> HFinite) = (x \<in> HFinite)"
by (simp add: HFinite_def)

lemma SReal_subset_HFinite: "Reals \<subseteq> HFinite"
apply (auto simp add: SReal_def HFinite_def)
apply (rule_tac x = "1 + abs (hypreal_of_real r) " in exI)
apply (auto simp add: hypreal_of_real_hrabs)
apply (rule_tac x = "1 + abs r" in exI, simp)
done

lemma HFinite_hypreal_of_real [simp]: "hypreal_of_real x \<in> HFinite"
by (auto intro: SReal_subset_HFinite [THEN subsetD])

lemma HFiniteD: "x \<in> HFinite ==> \<exists>t \<in> Reals. abs x < t"
by (simp add: HFinite_def)

lemma HFinite_hrabs_iff: "(abs x \<in> HFinite) = (x \<in> HFinite)"
by (simp add: HFinite_def)
declare HFinite_hrabs_iff [iff]

lemma HFinite_number_of: "number_of w \<in> HFinite"
by (rule SReal_number_of [THEN SReal_subset_HFinite [THEN subsetD]])
declare HFinite_number_of [simp]

(** As always with numerals, 0 and 1 are special cases **)

lemma HFinite_0: "0 \<in> HFinite"
apply (subst numeral_0_eq_0 [symmetric])
apply (rule HFinite_number_of)
done
declare HFinite_0 [simp]

lemma HFinite_1: "1 \<in> HFinite"
apply (subst numeral_1_eq_1 [symmetric])
apply (rule HFinite_number_of)
done
declare HFinite_1 [simp]

lemma HFinite_bounded: "[|x \<in> HFinite; y \<le> x; 0 \<le> y |] ==> y \<in> HFinite"
apply (case_tac "x \<le> 0")
apply (drule_tac y = x in order_trans)
apply (drule_tac [2] hypreal_le_anti_sym)
apply (auto simp add: linorder_not_le)
apply (auto intro: order_le_less_trans simp add: abs_if HFinite_def)
done


subsection{* Set of Infinitesimals is a Subring of the Hyperreals*}

lemma InfinitesimalD:
      "x \<in> Infinitesimal ==> \<forall>r \<in> Reals. 0 < r --> abs x < r"
by (simp add: Infinitesimal_def)

lemma Infinitesimal_zero: "0 \<in> Infinitesimal"
by (simp add: Infinitesimal_def)
declare Infinitesimal_zero [iff]

lemma hypreal_sum_of_halves: "x/(2::hypreal) + x/(2::hypreal) = x"
by auto

lemma Infinitesimal_add:
     "[| x \<in> Infinitesimal; y \<in> Infinitesimal |] ==> (x+y) \<in> Infinitesimal"
apply (auto simp add: Infinitesimal_def)
apply (rule hypreal_sum_of_halves [THEN subst])
apply (drule half_gt_zero)
apply (blast intro: hrabs_add_less hrabs_add_less SReal_divide_number_of)
done

lemma Infinitesimal_minus_iff: "(-x:Infinitesimal) = (x:Infinitesimal)"
by (simp add: Infinitesimal_def)
declare Infinitesimal_minus_iff [simp]

lemma Infinitesimal_diff:
     "[| x \<in> Infinitesimal;  y \<in> Infinitesimal |] ==> x-y \<in> Infinitesimal"
by (simp add: hypreal_diff_def Infinitesimal_add)

lemma Infinitesimal_mult:
     "[| x \<in> Infinitesimal; y \<in> Infinitesimal |] ==> (x * y) \<in> Infinitesimal"
apply (auto simp add: Infinitesimal_def)
apply (case_tac "y=0")
apply (cut_tac [2] a = "abs x" and b = 1 and c = "abs y" and d = r in mult_strict_mono, auto)
done

lemma Infinitesimal_HFinite_mult:
     "[| x \<in> Infinitesimal; y \<in> HFinite |] ==> (x * y) \<in> Infinitesimal"
apply (auto dest!: HFiniteD simp add: Infinitesimal_def)
apply (frule hrabs_less_gt_zero)
apply (drule_tac x = "r/t" in bspec)
apply (blast intro: SReal_divide)
apply (simp add: zero_less_divide_iff)
apply (case_tac "x=0 | y=0")
apply (cut_tac [2] a = "abs x" and b = "r/t" and c = "abs y" in mult_strict_mono)
apply (auto simp add: zero_less_divide_iff)
done

lemma Infinitesimal_HFinite_mult2:
     "[| x \<in> Infinitesimal; y \<in> HFinite |] ==> (y * x) \<in> Infinitesimal"
by (auto dest: Infinitesimal_HFinite_mult simp add: hypreal_mult_commute)

(*** rather long proof ***)
lemma HInfinite_inverse_Infinitesimal:
     "x \<in> HInfinite ==> inverse x: Infinitesimal"
apply (auto simp add: HInfinite_def Infinitesimal_def)
apply (erule_tac x = "inverse r" in ballE)
apply (frule_tac a1 = r and z = "abs x" in positive_imp_inverse_positive [THEN order_less_trans], assumption)
apply (drule inverse_inverse_eq [symmetric, THEN subst])
apply (rule inverse_less_iff_less [THEN iffD1])
apply (auto simp add: SReal_inverse)
done

lemma HInfinite_mult: "[|x \<in> HInfinite;y \<in> HInfinite|] ==> (x*y) \<in> HInfinite"
apply (simp add: HInfinite_def, auto)
apply (erule_tac x = 1 in ballE)
apply (erule_tac x = r in ballE)
apply (case_tac "y=0")
apply (cut_tac [2] c = 1 and d = "abs x" and a = r and b = "abs y" in mult_strict_mono)
apply (auto simp add: mult_ac)
done

lemma HInfinite_add_ge_zero:
      "[|x \<in> HInfinite; 0 \<le> y; 0 \<le> x|] ==> (x + y): HInfinite"
by (auto intro!: hypreal_add_zero_less_le_mono 
       simp add: abs_if hypreal_add_commute hypreal_le_add_order HInfinite_def)

lemma HInfinite_add_ge_zero2:
     "[|x \<in> HInfinite; 0 \<le> y; 0 \<le> x|] ==> (y + x): HInfinite"
by (auto intro!: HInfinite_add_ge_zero simp add: hypreal_add_commute)

lemma HInfinite_add_gt_zero:
     "[|x \<in> HInfinite; 0 < y; 0 < x|] ==> (x + y): HInfinite"
by (blast intro: HInfinite_add_ge_zero order_less_imp_le)

lemma HInfinite_minus_iff: "(-x \<in> HInfinite) = (x \<in> HInfinite)"
by (simp add: HInfinite_def)

lemma HInfinite_add_le_zero:
     "[|x \<in> HInfinite; y \<le> 0; x \<le> 0|] ==> (x + y): HInfinite"
apply (drule HInfinite_minus_iff [THEN iffD2])
apply (rule HInfinite_minus_iff [THEN iffD1])
apply (auto intro: HInfinite_add_ge_zero)
done

lemma HInfinite_add_lt_zero:
     "[|x \<in> HInfinite; y < 0; x < 0|] ==> (x + y): HInfinite"
by (blast intro: HInfinite_add_le_zero order_less_imp_le)

lemma HFinite_sum_squares:
     "[|a: HFinite; b: HFinite; c: HFinite|]
      ==> a*a + b*b + c*c \<in> HFinite"
by (auto intro: HFinite_mult HFinite_add)

lemma not_Infinitesimal_not_zero: "x \<notin> Infinitesimal ==> x \<noteq> 0"
by auto

lemma not_Infinitesimal_not_zero2: "x \<in> HFinite - Infinitesimal ==> x \<noteq> 0"
by auto

lemma Infinitesimal_hrabs_iff: "(abs x \<in> Infinitesimal) = (x \<in> Infinitesimal)"
by (auto simp add: hrabs_def)
declare Infinitesimal_hrabs_iff [iff]

lemma HFinite_diff_Infinitesimal_hrabs:
     "x \<in> HFinite - Infinitesimal ==> abs x \<in> HFinite - Infinitesimal"
by blast

lemma hrabs_less_Infinitesimal:
      "[| e \<in> Infinitesimal; abs x < e |] ==> x \<in> Infinitesimal"
by (auto simp add: Infinitesimal_def abs_less_iff)

lemma hrabs_le_Infinitesimal:
     "[| e \<in> Infinitesimal; abs x \<le> e |] ==> x \<in> Infinitesimal"
by (blast dest: order_le_imp_less_or_eq intro: hrabs_less_Infinitesimal)

lemma Infinitesimal_interval:
      "[| e \<in> Infinitesimal; e' \<in> Infinitesimal; e' < x ; x < e |] 
       ==> x \<in> Infinitesimal"
by (auto simp add: Infinitesimal_def abs_less_iff)

lemma Infinitesimal_interval2:
     "[| e \<in> Infinitesimal; e' \<in> Infinitesimal;
         e' \<le> x ; x \<le> e |] ==> x \<in> Infinitesimal"
by (auto intro: Infinitesimal_interval simp add: order_le_less)

lemma not_Infinitesimal_mult:
     "[| x \<notin> Infinitesimal;  y \<notin> Infinitesimal|] ==> (x*y) \<notin>Infinitesimal"
apply (unfold Infinitesimal_def, clarify)
apply (simp add: linorder_not_less)
apply (erule_tac x = "r*ra" in ballE)
prefer 2 apply (fast intro: SReal_mult)
apply (auto simp add: zero_less_mult_iff)
apply (cut_tac c = ra and d = "abs y" and a = r and b = "abs x" in mult_mono, auto)
done

lemma Infinitesimal_mult_disj:
     "x*y \<in> Infinitesimal ==> x \<in> Infinitesimal | y \<in> Infinitesimal"
apply (rule ccontr)
apply (drule de_Morgan_disj [THEN iffD1])
apply (fast dest: not_Infinitesimal_mult)
done

lemma HFinite_Infinitesimal_not_zero: "x \<in> HFinite-Infinitesimal ==> x \<noteq> 0"
by blast

lemma HFinite_Infinitesimal_diff_mult:
     "[| x \<in> HFinite - Infinitesimal;
                   y \<in> HFinite - Infinitesimal
                |] ==> (x*y) \<in> HFinite - Infinitesimal"
apply clarify
apply (blast dest: HFinite_mult not_Infinitesimal_mult)
done

lemma Infinitesimal_subset_HFinite:
      "Infinitesimal \<subseteq> HFinite"
apply (simp add: Infinitesimal_def HFinite_def, auto)
apply (rule_tac x = 1 in bexI, auto)
done

lemma Infinitesimal_hypreal_of_real_mult:
     "x \<in> Infinitesimal ==> x * hypreal_of_real r \<in> Infinitesimal"
by (erule HFinite_hypreal_of_real [THEN [2] Infinitesimal_HFinite_mult])

lemma Infinitesimal_hypreal_of_real_mult2:
     "x \<in> Infinitesimal ==> hypreal_of_real r * x \<in> Infinitesimal"
by (erule HFinite_hypreal_of_real [THEN [2] Infinitesimal_HFinite_mult2])


subsection{*The Infinitely Close Relation*}

lemma mem_infmal_iff: "(x \<in> Infinitesimal) = (x @= 0)"
by (simp add: Infinitesimal_def approx_def)

lemma approx_minus_iff: " (x @= y) = (x + -y @= 0)"
by (simp add: approx_def)

lemma approx_minus_iff2: " (x @= y) = (-y + x @= 0)"
by (simp add: approx_def hypreal_add_commute)

lemma approx_refl: "x @= x"
by (simp add: approx_def Infinitesimal_def)
declare approx_refl [iff]

lemma hypreal_minus_distrib1: "-(y + -(x::hypreal)) = x + -y"
by (simp add: hypreal_add_commute)

lemma approx_sym: "x @= y ==> y @= x"
apply (simp add: approx_def)
apply (rule hypreal_minus_distrib1 [THEN subst])
apply (erule Infinitesimal_minus_iff [THEN iffD2])
done

lemma approx_trans: "[| x @= y; y @= z |] ==> x @= z"
apply (simp add: approx_def)
apply (drule Infinitesimal_add, assumption, auto)
done

lemma approx_trans2: "[| r @= x; s @= x |] ==> r @= s"
by (blast intro: approx_sym approx_trans)

lemma approx_trans3: "[| x @= r; x @= s|] ==> r @= s"
by (blast intro: approx_sym approx_trans)

lemma number_of_approx_reorient: "(number_of w @= x) = (x @= number_of w)"
by (blast intro: approx_sym)

lemma zero_approx_reorient: "(0 @= x) = (x @= 0)"
by (blast intro: approx_sym)

lemma one_approx_reorient: "(1 @= x) = (x @= 1)"
by (blast intro: approx_sym)


ML
{*
val SReal_add = thm "SReal_add";
val SReal_mult = thm "SReal_mult";
val SReal_inverse = thm "SReal_inverse";
val SReal_divide = thm "SReal_divide";
val SReal_minus = thm "SReal_minus";
val SReal_minus_iff = thm "SReal_minus_iff";
val SReal_add_cancel = thm "SReal_add_cancel";
val SReal_hrabs = thm "SReal_hrabs";
val SReal_hypreal_of_real = thm "SReal_hypreal_of_real";
val SReal_number_of = thm "SReal_number_of";
val Reals_0 = thm "Reals_0";
val Reals_1 = thm "Reals_1";
val SReal_divide_number_of = thm "SReal_divide_number_of";
val SReal_epsilon_not_mem = thm "SReal_epsilon_not_mem";
val SReal_omega_not_mem = thm "SReal_omega_not_mem";
val SReal_UNIV_real = thm "SReal_UNIV_real";
val SReal_iff = thm "SReal_iff";
val hypreal_of_real_image = thm "hypreal_of_real_image";
val inv_hypreal_of_real_image = thm "inv_hypreal_of_real_image";
val SReal_hypreal_of_real_image = thm "SReal_hypreal_of_real_image";
val SReal_dense = thm "SReal_dense";
val SReal_sup_lemma = thm "SReal_sup_lemma";
val SReal_sup_lemma2 = thm "SReal_sup_lemma2";
val hypreal_of_real_isUb_iff = thm "hypreal_of_real_isUb_iff";
val hypreal_of_real_isLub1 = thm "hypreal_of_real_isLub1";
val hypreal_of_real_isLub2 = thm "hypreal_of_real_isLub2";
val hypreal_of_real_isLub_iff = thm "hypreal_of_real_isLub_iff";
val lemma_isUb_hypreal_of_real = thm "lemma_isUb_hypreal_of_real";
val lemma_isLub_hypreal_of_real = thm "lemma_isLub_hypreal_of_real";
val lemma_isLub_hypreal_of_real2 = thm "lemma_isLub_hypreal_of_real2";
val SReal_complete = thm "SReal_complete";
val HFinite_add = thm "HFinite_add";
val HFinite_mult = thm "HFinite_mult";
val HFinite_minus_iff = thm "HFinite_minus_iff";
val SReal_subset_HFinite = thm "SReal_subset_HFinite";
val HFinite_hypreal_of_real = thm "HFinite_hypreal_of_real";
val HFiniteD = thm "HFiniteD";
val HFinite_hrabs_iff = thm "HFinite_hrabs_iff";
val HFinite_number_of = thm "HFinite_number_of";
val HFinite_0 = thm "HFinite_0";
val HFinite_1 = thm "HFinite_1";
val HFinite_bounded = thm "HFinite_bounded";
val InfinitesimalD = thm "InfinitesimalD";
val Infinitesimal_zero = thm "Infinitesimal_zero";
val hypreal_sum_of_halves = thm "hypreal_sum_of_halves";
val Infinitesimal_add = thm "Infinitesimal_add";
val Infinitesimal_minus_iff = thm "Infinitesimal_minus_iff";
val Infinitesimal_diff = thm "Infinitesimal_diff";
val Infinitesimal_mult = thm "Infinitesimal_mult";
val Infinitesimal_HFinite_mult = thm "Infinitesimal_HFinite_mult";
val Infinitesimal_HFinite_mult2 = thm "Infinitesimal_HFinite_mult2";
val HInfinite_inverse_Infinitesimal = thm "HInfinite_inverse_Infinitesimal";
val HInfinite_mult = thm "HInfinite_mult";
val HInfinite_add_ge_zero = thm "HInfinite_add_ge_zero";
val HInfinite_add_ge_zero2 = thm "HInfinite_add_ge_zero2";
val HInfinite_add_gt_zero = thm "HInfinite_add_gt_zero";
val HInfinite_minus_iff = thm "HInfinite_minus_iff";
val HInfinite_add_le_zero = thm "HInfinite_add_le_zero";
val HInfinite_add_lt_zero = thm "HInfinite_add_lt_zero";
val HFinite_sum_squares = thm "HFinite_sum_squares";
val not_Infinitesimal_not_zero = thm "not_Infinitesimal_not_zero";
val not_Infinitesimal_not_zero2 = thm "not_Infinitesimal_not_zero2";
val Infinitesimal_hrabs_iff = thm "Infinitesimal_hrabs_iff";
val HFinite_diff_Infinitesimal_hrabs = thm "HFinite_diff_Infinitesimal_hrabs";
val hrabs_less_Infinitesimal = thm "hrabs_less_Infinitesimal";
val hrabs_le_Infinitesimal = thm "hrabs_le_Infinitesimal";
val Infinitesimal_interval = thm "Infinitesimal_interval";
val Infinitesimal_interval2 = thm "Infinitesimal_interval2";
val not_Infinitesimal_mult = thm "not_Infinitesimal_mult";
val Infinitesimal_mult_disj = thm "Infinitesimal_mult_disj";
val HFinite_Infinitesimal_not_zero = thm "HFinite_Infinitesimal_not_zero";
val HFinite_Infinitesimal_diff_mult = thm "HFinite_Infinitesimal_diff_mult";
val Infinitesimal_subset_HFinite = thm "Infinitesimal_subset_HFinite";
val Infinitesimal_hypreal_of_real_mult = thm "Infinitesimal_hypreal_of_real_mult";
val Infinitesimal_hypreal_of_real_mult2 = thm "Infinitesimal_hypreal_of_real_mult2";
val mem_infmal_iff = thm "mem_infmal_iff";
val approx_minus_iff = thm "approx_minus_iff";
val approx_minus_iff2 = thm "approx_minus_iff2";
val approx_refl = thm "approx_refl";
val approx_sym = thm "approx_sym";
val approx_trans = thm "approx_trans";
val approx_trans2 = thm "approx_trans2";
val approx_trans3 = thm "approx_trans3";
val number_of_approx_reorient = thm "number_of_approx_reorient";
val zero_approx_reorient = thm "zero_approx_reorient";
val one_approx_reorient = thm "one_approx_reorient";

(*** re-orientation, following HOL/Integ/Bin.ML
     We re-orient x @=y where x is 0, 1 or a numeral, unless y is as well!
 ***)

(*reorientation simprules using ==, for the following simproc*)
val meta_zero_approx_reorient = zero_approx_reorient RS eq_reflection;
val meta_one_approx_reorient = one_approx_reorient RS eq_reflection;
val meta_number_of_approx_reorient = number_of_approx_reorient RS eq_reflection

(*reorientation simplification procedure: reorients (polymorphic)
  0 = x, 1 = x, nnn = x provided x isn't 0, 1 or a numeral.*)
fun reorient_proc sg _ (_ $ t $ u) =
  case u of
      Const("0", _) => None
    | Const("1", _) => None
    | Const("Numeral.number_of", _) $ _ => None
    | _ => Some (case t of
                Const("0", _) => meta_zero_approx_reorient
              | Const("1", _) => meta_one_approx_reorient
              | Const("Numeral.number_of", _) $ _ =>
                                 meta_number_of_approx_reorient);

val approx_reorient_simproc =
  Bin_Simprocs.prep_simproc
    ("reorient_simproc", ["0@=x", "1@=x", "number_of w @= x"], reorient_proc);

Addsimprocs [approx_reorient_simproc];
*}

lemma Infinitesimal_approx_minus: "(x-y \<in> Infinitesimal) = (x @= y)"
by (auto simp add: hypreal_diff_def approx_minus_iff [symmetric] mem_infmal_iff)

lemma approx_monad_iff: "(x @= y) = (monad(x)=monad(y))"
apply (simp add: monad_def)
apply (auto dest: approx_sym elim!: approx_trans equalityCE)
done

lemma Infinitesimal_approx:
     "[| x \<in> Infinitesimal; y \<in> Infinitesimal |] ==> x @= y"
apply (simp add: mem_infmal_iff)
apply (blast intro: approx_trans approx_sym)
done

lemma approx_add: "[| a @= b; c @= d |] ==> a+c @= b+d"
proof (unfold approx_def)
  assume inf: "a + - b \<in> Infinitesimal" "c + - d \<in> Infinitesimal"
  have "a + c + - (b + d) = (a + - b) + (c + - d)" by arith
  also have "... \<in> Infinitesimal" using inf by (rule Infinitesimal_add)
  finally show "a + c + - (b + d) \<in> Infinitesimal" .
qed

lemma approx_minus: "a @= b ==> -a @= -b"
apply (rule approx_minus_iff [THEN iffD2, THEN approx_sym])
apply (drule approx_minus_iff [THEN iffD1])
apply (simp (no_asm) add: hypreal_add_commute)
done

lemma approx_minus2: "-a @= -b ==> a @= b"
by (auto dest: approx_minus)

lemma approx_minus_cancel: "(-a @= -b) = (a @= b)"
by (blast intro: approx_minus approx_minus2)

declare approx_minus_cancel [simp]

lemma approx_add_minus: "[| a @= b; c @= d |] ==> a + -c @= b + -d"
by (blast intro!: approx_add approx_minus)

lemma approx_mult1: "[| a @= b; c: HFinite|] ==> a*c @= b*c"
by (simp add: approx_def Infinitesimal_HFinite_mult minus_mult_left 
              left_distrib [symmetric] 
         del: minus_mult_left [symmetric])

lemma approx_mult2: "[|a @= b; c: HFinite|] ==> c*a @= c*b"
apply (simp (no_asm_simp) add: approx_mult1 hypreal_mult_commute)
done

lemma approx_mult_subst: "[|u @= v*x; x @= y; v \<in> HFinite|] ==> u @= v*y"
by (blast intro: approx_mult2 approx_trans)

lemma approx_mult_subst2: "[| u @= x*v; x @= y; v \<in> HFinite |] ==> u @= y*v"
by (blast intro: approx_mult1 approx_trans)

lemma approx_mult_subst_SReal:
     "[| u @= x*hypreal_of_real v; x @= y |] ==> u @= y*hypreal_of_real v"
by (auto intro: approx_mult_subst2)

lemma approx_eq_imp: "a = b ==> a @= b"
by (simp add: approx_def)

lemma Infinitesimal_minus_approx: "x \<in> Infinitesimal ==> -x @= x"
by (blast intro: Infinitesimal_minus_iff [THEN iffD2] 
                    mem_infmal_iff [THEN iffD1] approx_trans2)

lemma bex_Infinitesimal_iff: "(\<exists>y \<in> Infinitesimal. x + -z = y) = (x @= z)"
by (simp add: approx_def)

lemma bex_Infinitesimal_iff2: "(\<exists>y \<in> Infinitesimal. x = z + y) = (x @= z)"
by (force simp add: bex_Infinitesimal_iff [symmetric])

lemma Infinitesimal_add_approx: "[| y \<in> Infinitesimal; x + y = z |] ==> x @= z"
apply (rule bex_Infinitesimal_iff [THEN iffD1])
apply (drule Infinitesimal_minus_iff [THEN iffD2])
apply (auto simp add: minus_add_distrib hypreal_add_assoc [symmetric])
done

lemma Infinitesimal_add_approx_self: "y \<in> Infinitesimal ==> x @= x + y"
apply (rule bex_Infinitesimal_iff [THEN iffD1])
apply (drule Infinitesimal_minus_iff [THEN iffD2])
apply (auto simp add: minus_add_distrib hypreal_add_assoc [symmetric])
done

lemma Infinitesimal_add_approx_self2: "y \<in> Infinitesimal ==> x @= y + x"
by (auto dest: Infinitesimal_add_approx_self simp add: hypreal_add_commute)

lemma Infinitesimal_add_minus_approx_self: "y \<in> Infinitesimal ==> x @= x + -y"
by (blast intro!: Infinitesimal_add_approx_self Infinitesimal_minus_iff [THEN iffD2])

lemma Infinitesimal_add_cancel: "[| y \<in> Infinitesimal; x+y @= z|] ==> x @= z"
apply (drule_tac x = x in Infinitesimal_add_approx_self [THEN approx_sym])
apply (erule approx_trans3 [THEN approx_sym], assumption)
done

lemma Infinitesimal_add_right_cancel:
     "[| y \<in> Infinitesimal; x @= z + y|] ==> x @= z"
apply (drule_tac x = z in Infinitesimal_add_approx_self2 [THEN approx_sym])
apply (erule approx_trans3 [THEN approx_sym])
apply (simp add: hypreal_add_commute)
apply (erule approx_sym)
done

lemma approx_add_left_cancel: "d + b  @= d + c ==> b @= c"
apply (drule approx_minus_iff [THEN iffD1])
apply (simp add: minus_add_distrib approx_minus_iff [symmetric] add_ac)
done

lemma approx_add_right_cancel: "b + d @= c + d ==> b @= c"
apply (rule approx_add_left_cancel)
apply (simp add: hypreal_add_commute)
done

lemma approx_add_mono1: "b @= c ==> d + b @= d + c"
apply (rule approx_minus_iff [THEN iffD2])
apply (simp add: minus_add_distrib approx_minus_iff [symmetric] add_ac)
done

lemma approx_add_mono2: "b @= c ==> b + a @= c + a"
apply (simp (no_asm_simp) add: hypreal_add_commute approx_add_mono1)
done

lemma approx_add_left_iff: "(a + b @= a + c) = (b @= c)"
by (fast elim: approx_add_left_cancel approx_add_mono1)

declare approx_add_left_iff [simp]

lemma approx_add_right_iff: "(b + a @= c + a) = (b @= c)"
apply (simp (no_asm) add: hypreal_add_commute)
done

declare approx_add_right_iff [simp]

lemma approx_HFinite: "[| x \<in> HFinite; x @= y |] ==> y \<in> HFinite"
apply (drule bex_Infinitesimal_iff2 [THEN iffD2], safe)
apply (drule Infinitesimal_subset_HFinite [THEN subsetD, THEN HFinite_minus_iff [THEN iffD2]])
apply (drule HFinite_add)
apply (auto simp add: hypreal_add_assoc)
done

lemma approx_hypreal_of_real_HFinite: "x @= hypreal_of_real D ==> x \<in> HFinite"
by (rule approx_sym [THEN [2] approx_HFinite], auto)

lemma approx_mult_HFinite:
     "[|a @= b; c @= d; b: HFinite; d: HFinite|] ==> a*c @= b*d"
apply (rule approx_trans)
apply (rule_tac [2] approx_mult2)
apply (rule approx_mult1)
prefer 2 apply (blast intro: approx_HFinite approx_sym, auto)
done

lemma approx_mult_hypreal_of_real:
     "[|a @= hypreal_of_real b; c @= hypreal_of_real d |]
      ==> a*c @= hypreal_of_real b*hypreal_of_real d"
apply (blast intro!: approx_mult_HFinite approx_hypreal_of_real_HFinite HFinite_hypreal_of_real)
done

lemma approx_SReal_mult_cancel_zero:
     "[| a \<in> Reals; a \<noteq> 0; a*x @= 0 |] ==> x @= 0"
apply (drule SReal_inverse [THEN SReal_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: hypreal_mult_assoc [symmetric])
done

(* REM comments: newly added *)
lemma approx_mult_SReal1: "[| a \<in> Reals; x @= 0 |] ==> x*a @= 0"
by (auto dest: SReal_subset_HFinite [THEN subsetD] approx_mult1)

lemma approx_mult_SReal2: "[| a \<in> Reals; x @= 0 |] ==> a*x @= 0"
by (auto dest: SReal_subset_HFinite [THEN subsetD] approx_mult2)

lemma approx_mult_SReal_zero_cancel_iff:
     "[|a \<in> Reals; a \<noteq> 0 |] ==> (a*x @= 0) = (x @= 0)"
by (blast intro: approx_SReal_mult_cancel_zero approx_mult_SReal2)
declare approx_mult_SReal_zero_cancel_iff [simp]

lemma approx_SReal_mult_cancel:
     "[| a \<in> Reals; a \<noteq> 0; a* w @= a*z |] ==> w @= z"
apply (drule SReal_inverse [THEN SReal_subset_HFinite [THEN subsetD]])
apply (auto dest: approx_mult2 simp add: hypreal_mult_assoc [symmetric])
done

lemma approx_SReal_mult_cancel_iff1:
     "[| a \<in> Reals; a \<noteq> 0|] ==> (a* w @= a*z) = (w @= z)"
by (auto intro!: approx_mult2 SReal_subset_HFinite [THEN subsetD] intro: approx_SReal_mult_cancel)
declare approx_SReal_mult_cancel_iff1 [simp]

lemma approx_le_bound: "[| z \<le> f; f @= g; g \<le> z |] ==> f @= z"
apply (simp add: bex_Infinitesimal_iff2 [symmetric], auto)
apply (rule_tac x = "g+y-z" in bexI)
apply (simp (no_asm))
apply (rule Infinitesimal_interval2)
apply (rule_tac [2] Infinitesimal_zero, auto)
done


subsection{* Zero is the Only Infinitesimal that is Also a Real*}

lemma Infinitesimal_less_SReal:
     "[| x \<in> Reals; y \<in> Infinitesimal; 0 < x |] ==> y < x"
apply (simp add: Infinitesimal_def)
apply (rule abs_ge_self [THEN order_le_less_trans], auto)
done

lemma Infinitesimal_less_SReal2:
     "y \<in> Infinitesimal ==> \<forall>r \<in> Reals. 0 < r --> y < r"
by (blast intro: Infinitesimal_less_SReal)

lemma SReal_not_Infinitesimal:
     "[| 0 < y;  y \<in> Reals|] ==> y \<notin> Infinitesimal"
apply (simp add: Infinitesimal_def)
apply (auto simp add: hrabs_def)
done

lemma SReal_minus_not_Infinitesimal:
     "[| y < 0;  y \<in> Reals |] ==> y \<notin> Infinitesimal"
apply (subst Infinitesimal_minus_iff [symmetric])
apply (rule SReal_not_Infinitesimal, auto)
done

lemma SReal_Int_Infinitesimal_zero: "Reals Int Infinitesimal = {0}"
apply auto
apply (cut_tac x = x and y = 0 in linorder_less_linear)
apply (blast dest: SReal_not_Infinitesimal SReal_minus_not_Infinitesimal)
done

lemma SReal_Infinitesimal_zero: "[| x \<in> Reals; x \<in> Infinitesimal|] ==> x = 0"
by (cut_tac SReal_Int_Infinitesimal_zero, blast)

lemma SReal_HFinite_diff_Infinitesimal:
     "[| x \<in> Reals; x \<noteq> 0 |] ==> x \<in> HFinite - Infinitesimal"
by (auto dest: SReal_Infinitesimal_zero SReal_subset_HFinite [THEN subsetD])

lemma hypreal_of_real_HFinite_diff_Infinitesimal:
     "hypreal_of_real x \<noteq> 0 ==> hypreal_of_real x \<in> HFinite - Infinitesimal"
by (rule SReal_HFinite_diff_Infinitesimal, auto)

lemma hypreal_of_real_Infinitesimal_iff_0:
     "(hypreal_of_real x \<in> Infinitesimal) = (x=0)"
apply auto
apply (rule ccontr)
apply (rule hypreal_of_real_HFinite_diff_Infinitesimal [THEN DiffD2], auto)
done
declare hypreal_of_real_Infinitesimal_iff_0 [iff]

lemma number_of_not_Infinitesimal:
     "number_of w \<noteq> (0::hypreal) ==> number_of w \<notin> Infinitesimal"
by (fast dest: SReal_number_of [THEN SReal_Infinitesimal_zero])
declare number_of_not_Infinitesimal [simp]

(*again: 1 is a special case, but not 0 this time*)
lemma one_not_Infinitesimal: "1 \<notin> Infinitesimal"
apply (subst numeral_1_eq_1 [symmetric])
apply (rule number_of_not_Infinitesimal)
apply (simp (no_asm))
done
declare one_not_Infinitesimal [simp]

lemma approx_SReal_not_zero: "[| y \<in> Reals; x @= y; y\<noteq> 0 |] ==> x \<noteq> 0"
apply (cut_tac x = 0 and y = y in linorder_less_linear, simp)
apply (blast dest: approx_sym [THEN mem_infmal_iff [THEN iffD2]] SReal_not_Infinitesimal SReal_minus_not_Infinitesimal)
done

lemma HFinite_diff_Infinitesimal_approx:
     "[| x @= y; y \<in> HFinite - Infinitesimal |]
      ==> x \<in> HFinite - Infinitesimal"
apply (auto intro: approx_sym [THEN [2] approx_HFinite]
            simp add: mem_infmal_iff)
apply (drule approx_trans3, assumption)
apply (blast dest: approx_sym)
done

(*The premise y\<noteq>0 is essential; otherwise x/y =0 and we lose the
  HFinite premise.*)
lemma Infinitesimal_ratio:
     "[| y \<noteq> 0;  y \<in> Infinitesimal;  x/y \<in> HFinite |] ==> x \<in> Infinitesimal"
apply (drule Infinitesimal_HFinite_mult2, assumption)
apply (simp add: hypreal_divide_def hypreal_mult_assoc)
done

lemma Infinitesimal_SReal_divide: 
  "[| x \<in> Infinitesimal; y \<in> Reals |] ==> x/y \<in> Infinitesimal"
apply (simp add: divide_inverse)
apply (auto intro!: Infinitesimal_HFinite_mult 
            dest!: SReal_inverse [THEN SReal_subset_HFinite [THEN subsetD]])
done

(*------------------------------------------------------------------
       Standard Part Theorem: Every finite x: R* is infinitely
       close to a unique real number (i.e a member of Reals)
 ------------------------------------------------------------------*)

subsection{* Uniqueness: Two Infinitely Close Reals are Equal*}

lemma SReal_approx_iff: "[|x \<in> Reals; y \<in> Reals|] ==> (x @= y) = (x = y)"
apply auto
apply (simp add: approx_def)
apply (drule_tac x = y in SReal_minus)
apply (drule SReal_add, assumption)
apply (drule SReal_Infinitesimal_zero, assumption)
apply (drule sym)
apply (simp add: hypreal_eq_minus_iff [symmetric])
done

lemma number_of_approx_iff:
     "(number_of v @= number_of w) = (number_of v = (number_of w :: hypreal))"
by (auto simp add: SReal_approx_iff)
declare number_of_approx_iff [simp]

(*And also for 0 @= #nn and 1 @= #nn, #nn @= 0 and #nn @= 1.*)
lemma [simp]: "(0 @= number_of w) = ((number_of w :: hypreal) = 0)"
              "(number_of w @= 0) = ((number_of w :: hypreal) = 0)"
              "(1 @= number_of w) = ((number_of w :: hypreal) = 1)"
              "(number_of w @= 1) = ((number_of w :: hypreal) = 1)"
              "~ (0 @= 1)" "~ (1 @= 0)"
by (auto simp only: SReal_number_of SReal_approx_iff Reals_0 Reals_1)

lemma hypreal_of_real_approx_iff:
     "(hypreal_of_real k @= hypreal_of_real m) = (k = m)"
apply auto
apply (rule inj_hypreal_of_real [THEN injD])
apply (rule SReal_approx_iff [THEN iffD1], auto)
done
declare hypreal_of_real_approx_iff [simp]

lemma hypreal_of_real_approx_number_of_iff:
     "(hypreal_of_real k @= number_of w) = (k = number_of w)"
by (subst hypreal_of_real_approx_iff [symmetric], auto)
declare hypreal_of_real_approx_number_of_iff [simp]

(*And also for 0 and 1.*)
(*And also for 0 @= #nn and 1 @= #nn, #nn @= 0 and #nn @= 1.*)
lemma [simp]: "(hypreal_of_real k @= 0) = (k = 0)"
              "(hypreal_of_real k @= 1) = (k = 1)"
  by (simp_all add:  hypreal_of_real_approx_iff [symmetric])

lemma approx_unique_real:
     "[| r \<in> Reals; s \<in> Reals; r @= x; s @= x|] ==> r = s"
by (blast intro: SReal_approx_iff [THEN iffD1] approx_trans2)


subsection{* Existence of Unique Real Infinitely Close*}

(* lemma about lubs *)
lemma hypreal_isLub_unique:
     "[| isLub R S x; isLub R S y |] ==> x = (y::hypreal)"
apply (frule isLub_isUb)
apply (frule_tac x = y in isLub_isUb)
apply (blast intro!: hypreal_le_anti_sym dest!: isLub_le_isUb)
done

lemma lemma_st_part_ub:
     "x \<in> HFinite ==> \<exists>u. isUb Reals {s. s \<in> Reals & s < x} u"
apply (drule HFiniteD, safe)
apply (rule exI, rule isUbI)
apply (auto intro: setleI isUbI simp add: abs_less_iff)
done

lemma lemma_st_part_nonempty: "x \<in> HFinite ==> \<exists>y. y \<in> {s. s \<in> Reals & s < x}"
apply (drule HFiniteD, safe)
apply (drule SReal_minus)
apply (rule_tac x = "-t" in exI)
apply (auto simp add: abs_less_iff)
done

lemma lemma_st_part_subset: "{s. s \<in> Reals & s < x} \<subseteq> Reals"
by auto

lemma lemma_st_part_lub:
     "x \<in> HFinite ==> \<exists>t. isLub Reals {s. s \<in> Reals & s < x} t"
by (blast intro!: SReal_complete lemma_st_part_ub lemma_st_part_nonempty lemma_st_part_subset)

lemma lemma_hypreal_le_left_cancel: "((t::hypreal) + r \<le> t) = (r \<le> 0)"
apply safe
apply (drule_tac c = "-t" in add_left_mono)
apply (drule_tac [2] c = t in add_left_mono)
apply (auto simp add: hypreal_add_assoc [symmetric])
done

lemma lemma_st_part_le1:
     "[| x \<in> HFinite;  isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals;  0 < r |] ==> x \<le> t + r"
apply (frule isLubD1a)
apply (rule ccontr, drule linorder_not_le [THEN iffD2])
apply (drule_tac x = t in SReal_add, assumption)
apply (drule_tac y = "t + r" in isLubD1 [THEN setleD], auto)
done

lemma hypreal_setle_less_trans:
     "!!x::hypreal. [| S *<= x; x < y |] ==> S *<= y"
apply (simp add: setle_def)
apply (auto dest!: bspec order_le_less_trans intro: order_less_imp_le)
done

lemma hypreal_gt_isUb:
     "!!x::hypreal. [| isUb R S x; x < y; y \<in> R |] ==> isUb R S y"
apply (simp add: isUb_def)
apply (blast intro: hypreal_setle_less_trans)
done

lemma lemma_st_part_gt_ub:
     "[| x \<in> HFinite; x < y; y \<in> Reals |]
      ==> isUb Reals {s. s \<in> Reals & s < x} y"
by (auto dest: order_less_trans intro: order_less_imp_le intro!: isUbI setleI)

lemma lemma_minus_le_zero: "t \<le> t + -r ==> r \<le> (0::hypreal)"
apply (drule_tac c = "-t" in add_left_mono)
apply (auto simp add: hypreal_add_assoc [symmetric])
done

lemma lemma_st_part_le2:
     "[| x \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> t + -r \<le> x"
apply (frule isLubD1a)
apply (rule ccontr, drule linorder_not_le [THEN iffD1])
apply (drule SReal_minus, drule_tac x = t in SReal_add, assumption)
apply (drule lemma_st_part_gt_ub, assumption+)
apply (drule isLub_le_isUb, assumption)
apply (drule lemma_minus_le_zero)
apply (auto dest: order_less_le_trans)
done

lemma lemma_hypreal_le_swap: "((x::hypreal) \<le> t + r) = (x + -t \<le> r)"
by auto

lemma lemma_st_part1a:
     "[| x \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> x + -t \<le> r"
by (blast intro!: lemma_hypreal_le_swap [THEN iffD1] lemma_st_part_le1)

lemma lemma_hypreal_le_swap2: "(t + -r \<le> x) = (-(x + -t) \<le> (r::hypreal))"
by auto

lemma lemma_st_part2a:
     "[| x \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals;  0 < r |]
      ==> -(x + -t) \<le> r"
apply (blast intro!: lemma_hypreal_le_swap2 [THEN iffD1] lemma_st_part_le2)
done

lemma lemma_SReal_ub:
     "(x::hypreal) \<in> Reals ==> isUb Reals {s. s \<in> Reals & s < x} x"
by (auto intro: isUbI setleI order_less_imp_le)

lemma lemma_SReal_lub:
     "(x::hypreal) \<in> Reals ==> isLub Reals {s. s \<in> Reals & s < x} x"
apply (auto intro!: isLubI2 lemma_SReal_ub setgeI)
apply (frule isUbD2a)
apply (rule_tac x = x and y = y in linorder_cases)
apply (auto intro!: order_less_imp_le)
apply (drule SReal_dense, assumption, assumption, safe)
apply (drule_tac y = r in isUbD)
apply (auto dest: order_less_le_trans)
done

lemma lemma_st_part_not_eq1:
     "[| x \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> x + -t \<noteq> r"
apply auto
apply (frule isLubD1a [THEN SReal_minus])
apply (drule SReal_add_cancel, assumption)
apply (drule_tac x = x in lemma_SReal_lub)
apply (drule hypreal_isLub_unique, assumption, auto)
done

lemma lemma_st_part_not_eq2:
     "[| x \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> -(x + -t) \<noteq> r"
apply (auto simp add: minus_add_distrib)
apply (frule isLubD1a)
apply (drule SReal_add_cancel, assumption)
apply (drule_tac x = "-x" in SReal_minus, simp)
apply (drule_tac x = x in lemma_SReal_lub)
apply (drule hypreal_isLub_unique, assumption, auto)
done

lemma lemma_st_part_major:
     "[| x \<in> HFinite;
         isLub Reals {s. s \<in> Reals & s < x} t;
         r \<in> Reals; 0 < r |]
      ==> abs (x + -t) < r"
apply (frule lemma_st_part1a)
apply (frule_tac [4] lemma_st_part2a, auto)
apply (drule order_le_imp_less_or_eq)+
apply (auto dest: lemma_st_part_not_eq1 lemma_st_part_not_eq2 simp add: abs_less_iff)
done

lemma lemma_st_part_major2:
     "[| x \<in> HFinite; isLub Reals {s. s \<in> Reals & s < x} t |]
      ==> \<forall>r \<in> Reals. 0 < r --> abs (x + -t) < r"
by (blast dest!: lemma_st_part_major)

(*----------------------------------------------
  Existence of real and Standard Part Theorem
 ----------------------------------------------*)
lemma lemma_st_part_Ex:
     "x \<in> HFinite ==> \<exists>t \<in> Reals. \<forall>r \<in> Reals. 0 < r --> abs (x + -t) < r"
apply (frule lemma_st_part_lub, safe)
apply (frule isLubD1a)
apply (blast dest: lemma_st_part_major2)
done

lemma st_part_Ex:
     "x \<in> HFinite ==> \<exists>t \<in> Reals. x @= t"
apply (simp add: approx_def Infinitesimal_def)
apply (drule lemma_st_part_Ex, auto)
done

(*--------------------------------
  Unique real infinitely close
 -------------------------------*)
lemma st_part_Ex1: "x \<in> HFinite ==> EX! t. t \<in> Reals & x @= t"
apply (drule st_part_Ex, safe)
apply (drule_tac [2] approx_sym, drule_tac [2] approx_sym, drule_tac [2] approx_sym)
apply (auto intro!: approx_unique_real)
done

subsection{* Finite, Infinite and Infinitesimal*}

lemma HFinite_Int_HInfinite_empty: "HFinite Int HInfinite = {}"

apply (simp add: HFinite_def HInfinite_def)
apply (auto dest: order_less_trans)
done
declare HFinite_Int_HInfinite_empty [simp]

lemma HFinite_not_HInfinite: 
  assumes x: "x \<in> HFinite" shows "x \<notin> HInfinite"
proof
  assume x': "x \<in> HInfinite"
  with x have "x \<in> HFinite \<inter> HInfinite" by blast
  thus False by auto
qed

lemma not_HFinite_HInfinite: "x\<notin> HFinite ==> x \<in> HInfinite"
apply (simp add: HInfinite_def HFinite_def, auto)
apply (drule_tac x = "r + 1" in bspec)
apply (auto simp add: SReal_add)
done

lemma HInfinite_HFinite_disj: "x \<in> HInfinite | x \<in> HFinite"
by (blast intro: not_HFinite_HInfinite)

lemma HInfinite_HFinite_iff: "(x \<in> HInfinite) = (x \<notin> HFinite)"
by (blast dest: HFinite_not_HInfinite not_HFinite_HInfinite)

lemma HFinite_HInfinite_iff: "(x \<in> HFinite) = (x \<notin> HInfinite)"
by (simp add: HInfinite_HFinite_iff)


lemma HInfinite_diff_HFinite_Infinitesimal_disj:
     "x \<notin> Infinitesimal ==> x \<in> HInfinite | x \<in> HFinite - Infinitesimal"
by (fast intro: not_HFinite_HInfinite)

lemma HFinite_inverse:
     "[| x \<in> HFinite; x \<notin> Infinitesimal |] ==> inverse x \<in> HFinite"
apply (cut_tac x = "inverse x" in HInfinite_HFinite_disj)
apply (auto dest!: HInfinite_inverse_Infinitesimal)
done

lemma HFinite_inverse2: "x \<in> HFinite - Infinitesimal ==> inverse x \<in> HFinite"
by (blast intro: HFinite_inverse)

(* stronger statement possible in fact *)
lemma Infinitesimal_inverse_HFinite:
     "x \<notin> Infinitesimal ==> inverse(x) \<in> HFinite"
apply (drule HInfinite_diff_HFinite_Infinitesimal_disj)
apply (blast intro: HFinite_inverse HInfinite_inverse_Infinitesimal Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma HFinite_not_Infinitesimal_inverse:
     "x \<in> HFinite - Infinitesimal ==> inverse x \<in> HFinite - Infinitesimal"
apply (auto intro: Infinitesimal_inverse_HFinite)
apply (drule Infinitesimal_HFinite_mult2, assumption)
apply (simp add: not_Infinitesimal_not_zero hypreal_mult_inverse)
done

lemma approx_inverse:
     "[| x @= y; y \<in>  HFinite - Infinitesimal |]
      ==> inverse x @= inverse y"
apply (frule HFinite_diff_Infinitesimal_approx, assumption)
apply (frule not_Infinitesimal_not_zero2)
apply (frule_tac x = x in not_Infinitesimal_not_zero2)
apply (drule HFinite_inverse2)+
apply (drule approx_mult2, assumption, auto)
apply (drule_tac c = "inverse x" in approx_mult1, assumption)
apply (auto intro: approx_sym simp add: hypreal_mult_assoc)
done

(*Used for NSLIM_inverse, NSLIMSEQ_inverse*)
lemmas hypreal_of_real_approx_inverse =  hypreal_of_real_HFinite_diff_Infinitesimal [THEN [2] approx_inverse]

lemma inverse_add_Infinitesimal_approx:
     "[| x \<in> HFinite - Infinitesimal;
         h \<in> Infinitesimal |] ==> inverse(x + h) @= inverse x"
apply (auto intro: approx_inverse approx_sym Infinitesimal_add_approx_self)
done

lemma inverse_add_Infinitesimal_approx2:
     "[| x \<in> HFinite - Infinitesimal;
         h \<in> Infinitesimal |] ==> inverse(h + x) @= inverse x"
apply (rule hypreal_add_commute [THEN subst])
apply (blast intro: inverse_add_Infinitesimal_approx)
done

lemma inverse_add_Infinitesimal_approx_Infinitesimal:
     "[| x \<in> HFinite - Infinitesimal;
         h \<in> Infinitesimal |] ==> inverse(x + h) + -inverse x @= h"
apply (rule approx_trans2)
apply (auto intro: inverse_add_Infinitesimal_approx simp add: mem_infmal_iff approx_minus_iff [symmetric])
done

lemma Infinitesimal_square_iff: "(x \<in> Infinitesimal) = (x*x \<in> Infinitesimal)"
apply (auto intro: Infinitesimal_mult)
apply (rule ccontr, frule Infinitesimal_inverse_HFinite)
apply (frule not_Infinitesimal_not_zero)
apply (auto dest: Infinitesimal_HFinite_mult simp add: hypreal_mult_assoc)
done
declare Infinitesimal_square_iff [symmetric, simp]

lemma HFinite_square_iff: "(x*x \<in> HFinite) = (x \<in> HFinite)"
apply (auto intro: HFinite_mult)
apply (auto dest: HInfinite_mult simp add: HFinite_HInfinite_iff)
done
declare HFinite_square_iff [simp]

lemma HInfinite_square_iff: "(x*x \<in> HInfinite) = (x \<in> HInfinite)"
by (auto simp add: HInfinite_HFinite_iff)
declare HInfinite_square_iff [simp]

lemma approx_HFinite_mult_cancel:
     "[| a: HFinite-Infinitesimal; a* w @= a*z |] ==> w @= z"
apply safe
apply (frule HFinite_inverse, assumption)
apply (drule not_Infinitesimal_not_zero)
apply (auto dest: approx_mult2 simp add: hypreal_mult_assoc [symmetric])
done

lemma approx_HFinite_mult_cancel_iff1:
     "a: HFinite-Infinitesimal ==> (a * w @= a * z) = (w @= z)"
by (auto intro: approx_mult2 approx_HFinite_mult_cancel)

lemma HInfinite_HFinite_add_cancel:
     "[| x + y \<in> HInfinite; y \<in> HFinite |] ==> x \<in> HInfinite"
apply (rule ccontr)
apply (drule HFinite_HInfinite_iff [THEN iffD2])
apply (auto dest: HFinite_add simp add: HInfinite_HFinite_iff)
done

lemma HInfinite_HFinite_add:
     "[| x \<in> HInfinite; y \<in> HFinite |] ==> x + y \<in> HInfinite"
apply (rule_tac y = "-y" in HInfinite_HFinite_add_cancel)
apply (auto simp add: hypreal_add_assoc HFinite_minus_iff)
done

lemma HInfinite_ge_HInfinite:
     "[| x \<in> HInfinite; x \<le> y; 0 \<le> x |] ==> y \<in> HInfinite"
by (auto intro: HFinite_bounded simp add: HInfinite_HFinite_iff)

lemma Infinitesimal_inverse_HInfinite:
     "[| x \<in> Infinitesimal; x \<noteq> 0 |] ==> inverse x \<in> HInfinite"
apply (rule ccontr, drule HFinite_HInfinite_iff [THEN iffD2])
apply (auto dest: Infinitesimal_HFinite_mult2)
done

lemma HInfinite_HFinite_not_Infinitesimal_mult:
     "[| x \<in> HInfinite; y \<in> HFinite - Infinitesimal |]
      ==> x * y \<in> HInfinite"
apply (rule ccontr, drule HFinite_HInfinite_iff [THEN iffD2])
apply (frule HFinite_Infinitesimal_not_zero)
apply (drule HFinite_not_Infinitesimal_inverse)
apply (safe, drule HFinite_mult)
apply (auto simp add: hypreal_mult_assoc HFinite_HInfinite_iff)
done

lemma HInfinite_HFinite_not_Infinitesimal_mult2:
     "[| x \<in> HInfinite; y \<in> HFinite - Infinitesimal |]
      ==> y * x \<in> HInfinite"
by (auto simp add: hypreal_mult_commute HInfinite_HFinite_not_Infinitesimal_mult)

lemma HInfinite_gt_SReal: "[| x \<in> HInfinite; 0 < x; y \<in> Reals |] ==> y < x"
by (auto dest!: bspec simp add: HInfinite_def hrabs_def order_less_imp_le)

lemma HInfinite_gt_zero_gt_one: "[| x \<in> HInfinite; 0 < x |] ==> 1 < x"
by (auto intro: HInfinite_gt_SReal)


lemma not_HInfinite_one: "1 \<notin> HInfinite"
apply (simp (no_asm) add: HInfinite_HFinite_iff)
done
declare not_HInfinite_one [simp]

lemma approx_hrabs_disj: "abs x @= x | abs x @= -x"
by (cut_tac x = x in hrabs_disj, auto)


subsection{*Theorems about Monads*}

lemma monad_hrabs_Un_subset: "monad (abs x) \<le> monad(x) Un monad(-x)"
by (rule_tac x1 = x in hrabs_disj [THEN disjE], auto)

lemma Infinitesimal_monad_eq: "e \<in> Infinitesimal ==> monad (x+e) = monad x"
by (fast intro!: Infinitesimal_add_approx_self [THEN approx_sym] approx_monad_iff [THEN iffD1])

lemma mem_monad_iff: "(u \<in> monad x) = (-u \<in> monad (-x))"
by (simp add: monad_def)

lemma Infinitesimal_monad_zero_iff: "(x \<in> Infinitesimal) = (x \<in> monad 0)"
by (auto intro: approx_sym simp add: monad_def mem_infmal_iff)

lemma monad_zero_minus_iff: "(x \<in> monad 0) = (-x \<in> monad 0)"
apply (simp (no_asm) add: Infinitesimal_monad_zero_iff [symmetric])
done

lemma monad_zero_hrabs_iff: "(x \<in> monad 0) = (abs x \<in> monad 0)"
apply (rule_tac x1 = x in hrabs_disj [THEN disjE])
apply (auto simp add: monad_zero_minus_iff [symmetric])
done

lemma mem_monad_self: "x \<in> monad x"
by (simp add: monad_def)
declare mem_monad_self [simp]

(*------------------------------------------------------------------
         Proof that x @= y ==> abs x @= abs y
 ------------------------------------------------------------------*)
lemma approx_subset_monad: "x @= y ==> {x,y}\<le>monad x"
apply (simp (no_asm))
apply (simp add: approx_monad_iff)
done

lemma approx_subset_monad2: "x @= y ==> {x,y}\<le>monad y"
apply (drule approx_sym)
apply (fast dest: approx_subset_monad)
done

lemma mem_monad_approx: "u \<in> monad x ==> x @= u"
by (simp add: monad_def)

lemma approx_mem_monad: "x @= u ==> u \<in> monad x"
by (simp add: monad_def)

lemma approx_mem_monad2: "x @= u ==> x \<in> monad u"
apply (simp add: monad_def)
apply (blast intro!: approx_sym)
done

lemma approx_mem_monad_zero: "[| x @= y;x \<in> monad 0 |] ==> y \<in> monad 0"
apply (drule mem_monad_approx)
apply (fast intro: approx_mem_monad approx_trans)
done

lemma Infinitesimal_approx_hrabs:
     "[| x @= y; x \<in> Infinitesimal |] ==> abs x @= abs y"
apply (drule Infinitesimal_monad_zero_iff [THEN iffD1])
apply (blast intro: approx_mem_monad_zero monad_zero_hrabs_iff [THEN iffD1] mem_monad_approx approx_trans3)
done

lemma less_Infinitesimal_less:
     "[| 0 < x;  x \<notin>Infinitesimal;  e :Infinitesimal |] ==> e < x"
apply (rule ccontr)
apply (auto intro: Infinitesimal_zero [THEN [2] Infinitesimal_interval] 
            dest!: order_le_imp_less_or_eq simp add: linorder_not_less)
done

lemma Ball_mem_monad_gt_zero:
     "[| 0 < x;  x \<notin> Infinitesimal; u \<in> monad x |] ==> 0 < u"
apply (drule mem_monad_approx [THEN approx_sym])
apply (erule bex_Infinitesimal_iff2 [THEN iffD2, THEN bexE])
apply (drule_tac e = "-xa" in less_Infinitesimal_less, auto)
done

lemma Ball_mem_monad_less_zero:
     "[| x < 0; x \<notin> Infinitesimal; u \<in> monad x |] ==> u < 0"
apply (drule mem_monad_approx [THEN approx_sym])
apply (erule bex_Infinitesimal_iff [THEN iffD2, THEN bexE])
apply (cut_tac x = "-x" and e = xa in less_Infinitesimal_less, auto)
done

lemma lemma_approx_gt_zero:
     "[|0 < x; x \<notin> Infinitesimal; x @= y|] ==> 0 < y"
by (blast dest: Ball_mem_monad_gt_zero approx_subset_monad)

lemma lemma_approx_less_zero:
     "[|x < 0; x \<notin> Infinitesimal; x @= y|] ==> y < 0"
by (blast dest: Ball_mem_monad_less_zero approx_subset_monad)

lemma approx_hrabs1:
     "[| x @= y; x < 0; x \<notin> Infinitesimal |] ==> abs x @= abs y"
apply (frule lemma_approx_less_zero)
apply (assumption+)
apply (simp add: abs_if) 
done

lemma approx_hrabs2:
     "[| x @= y; 0 < x; x \<notin> Infinitesimal |] ==> abs x @= abs y"
apply (frule lemma_approx_gt_zero)
apply (assumption+)
apply (simp add: abs_if) 
done

lemma approx_hrabs: "x @= y ==> abs x @= abs y"
apply (rule_tac Q = "x \<in> Infinitesimal" in excluded_middle [THEN disjE])
apply (rule_tac x1 = x and y1 = 0 in linorder_less_linear [THEN disjE])
apply (auto intro: approx_hrabs1 approx_hrabs2 Infinitesimal_approx_hrabs)
done

lemma approx_hrabs_zero_cancel: "abs(x) @= 0 ==> x @= 0"
apply (cut_tac x = x in hrabs_disj)
apply (auto dest: approx_minus)
done

lemma approx_hrabs_add_Infinitesimal: "e \<in> Infinitesimal ==> abs x @= abs(x+e)"
by (fast intro: approx_hrabs Infinitesimal_add_approx_self)

lemma approx_hrabs_add_minus_Infinitesimal:
     "e \<in> Infinitesimal ==> abs x @= abs(x + -e)"
by (fast intro: approx_hrabs Infinitesimal_add_minus_approx_self)

lemma hrabs_add_Infinitesimal_cancel:
     "[| e \<in> Infinitesimal; e' \<in> Infinitesimal;
         abs(x+e) = abs(y+e')|] ==> abs x @= abs y"
apply (drule_tac x = x in approx_hrabs_add_Infinitesimal)
apply (drule_tac x = y in approx_hrabs_add_Infinitesimal)
apply (auto intro: approx_trans2)
done

lemma hrabs_add_minus_Infinitesimal_cancel:
     "[| e \<in> Infinitesimal; e' \<in> Infinitesimal;
         abs(x + -e) = abs(y + -e')|] ==> abs x @= abs y"
apply (drule_tac x = x in approx_hrabs_add_minus_Infinitesimal)
apply (drule_tac x = y in approx_hrabs_add_minus_Infinitesimal)
apply (auto intro: approx_trans2)
done

lemma hypreal_less_minus_iff: "((x::hypreal) < y) = (0 < y + -x)"
by arith

(* interesting slightly counterintuitive theorem: necessary
   for proving that an open interval is an NS open set
*)
lemma Infinitesimal_add_hypreal_of_real_less:
     "[| x < y;  u \<in> Infinitesimal |]
      ==> hypreal_of_real x + u < hypreal_of_real y"
apply (simp add: Infinitesimal_def)
apply (drule_tac x = "hypreal_of_real y + -hypreal_of_real x" in bspec, simp)  
apply (auto simp add: add_commute abs_less_iff SReal_add SReal_minus)
apply (simp add: compare_rls) 
done

lemma Infinitesimal_add_hrabs_hypreal_of_real_less:
     "[| x \<in> Infinitesimal; abs(hypreal_of_real r) < hypreal_of_real y |]
      ==> abs (hypreal_of_real r + x) < hypreal_of_real y"
apply (drule_tac x = "hypreal_of_real r" in approx_hrabs_add_Infinitesimal)
apply (drule approx_sym [THEN bex_Infinitesimal_iff2 [THEN iffD2]])
apply (auto intro!: Infinitesimal_add_hypreal_of_real_less simp add: hypreal_of_real_hrabs)
done

lemma Infinitesimal_add_hrabs_hypreal_of_real_less2:
     "[| x \<in> Infinitesimal;  abs(hypreal_of_real r) < hypreal_of_real y |]
      ==> abs (x + hypreal_of_real r) < hypreal_of_real y"
apply (rule hypreal_add_commute [THEN subst])
apply (erule Infinitesimal_add_hrabs_hypreal_of_real_less, assumption)
done

lemma hypreal_of_real_le_add_Infininitesimal_cancel:
     "[| u \<in> Infinitesimal; v \<in> Infinitesimal;
         hypreal_of_real x + u \<le> hypreal_of_real y + v |]
      ==> hypreal_of_real x \<le> hypreal_of_real y"
apply (simp add: linorder_not_less [symmetric], auto)
apply (drule_tac u = "v-u" in Infinitesimal_add_hypreal_of_real_less)
apply (auto simp add: Infinitesimal_diff)
done

lemma hypreal_of_real_le_add_Infininitesimal_cancel2:
     "[| u \<in> Infinitesimal; v \<in> Infinitesimal;
         hypreal_of_real x + u \<le> hypreal_of_real y + v |]
      ==> x \<le> y"
apply (blast intro!: hypreal_of_real_le_iff [THEN iffD1] hypreal_of_real_le_add_Infininitesimal_cancel)
done

lemma hypreal_of_real_less_Infinitesimal_le_zero:
     "[| hypreal_of_real x < e; e \<in> Infinitesimal |] ==> hypreal_of_real x \<le> 0"
apply (rule linorder_not_less [THEN iffD1], safe)
apply (drule Infinitesimal_interval)
apply (drule_tac [4] SReal_hypreal_of_real [THEN SReal_Infinitesimal_zero], auto)
done

(*used once, in Lim/NSDERIV_inverse*)
lemma Infinitesimal_add_not_zero:
     "[| h \<in> Infinitesimal; x \<noteq> 0 |] ==> hypreal_of_real x + h \<noteq> 0"
apply auto
apply (subgoal_tac "h = - hypreal_of_real x", auto)
done

lemma Infinitesimal_square_cancel:
     "x*x + y*y \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_interval2)
apply (rule_tac [3] zero_le_square, assumption)
apply (auto simp add: zero_le_square)
done
declare Infinitesimal_square_cancel [simp]

lemma HFinite_square_cancel: "x*x + y*y \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_bounded, assumption)
apply (auto simp add: zero_le_square)
done
declare HFinite_square_cancel [simp]

lemma Infinitesimal_square_cancel2:
     "x*x + y*y \<in> Infinitesimal ==> y*y \<in> Infinitesimal"
apply (rule Infinitesimal_square_cancel)
apply (rule hypreal_add_commute [THEN subst])
apply (simp (no_asm))
done
declare Infinitesimal_square_cancel2 [simp]

lemma HFinite_square_cancel2: "x*x + y*y \<in> HFinite ==> y*y \<in> HFinite"
apply (rule HFinite_square_cancel)
apply (rule hypreal_add_commute [THEN subst])
apply (simp (no_asm))
done
declare HFinite_square_cancel2 [simp]

lemma Infinitesimal_sum_square_cancel:
     "x*x + y*y + z*z \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_interval2, assumption)
apply (rule_tac [2] zero_le_square, simp)
apply (insert zero_le_square [of y]) 
apply (insert zero_le_square [of z], simp)
done
declare Infinitesimal_sum_square_cancel [simp]

lemma HFinite_sum_square_cancel: "x*x + y*y + z*z \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_bounded, assumption)
apply (rule_tac [2] zero_le_square)
apply (insert zero_le_square [of y]) 
apply (insert zero_le_square [of z], simp)
done
declare HFinite_sum_square_cancel [simp]

lemma Infinitesimal_sum_square_cancel2:
     "y*y + x*x + z*z \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_sum_square_cancel)
apply (simp add: add_ac)
done
declare Infinitesimal_sum_square_cancel2 [simp]

lemma HFinite_sum_square_cancel2:
     "y*y + x*x + z*z \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_sum_square_cancel)
apply (simp add: add_ac)
done
declare HFinite_sum_square_cancel2 [simp]

lemma Infinitesimal_sum_square_cancel3:
     "z*z + y*y + x*x \<in> Infinitesimal ==> x*x \<in> Infinitesimal"
apply (rule Infinitesimal_sum_square_cancel)
apply (simp add: add_ac)
done
declare Infinitesimal_sum_square_cancel3 [simp]

lemma HFinite_sum_square_cancel3:
     "z*z + y*y + x*x \<in> HFinite ==> x*x \<in> HFinite"
apply (rule HFinite_sum_square_cancel)
apply (simp add: add_ac)
done
declare HFinite_sum_square_cancel3 [simp]

lemma monad_hrabs_less: "[| y \<in> monad x; 0 < hypreal_of_real e |]
      ==> abs (y + -x) < hypreal_of_real e"
apply (drule mem_monad_approx [THEN approx_sym])
apply (drule bex_Infinitesimal_iff [THEN iffD2])
apply (auto dest!: InfinitesimalD)
done

lemma mem_monad_SReal_HFinite:
     "x \<in> monad (hypreal_of_real  a) ==> x \<in> HFinite"
apply (drule mem_monad_approx [THEN approx_sym])
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])
apply (safe dest!: Infinitesimal_subset_HFinite [THEN subsetD])
apply (erule SReal_hypreal_of_real [THEN SReal_subset_HFinite [THEN subsetD], THEN HFinite_add])
done


subsection{* Theorems about Standard Part*}

lemma st_approx_self: "x \<in> HFinite ==> st x @= x"
apply (simp add: st_def)
apply (frule st_part_Ex, safe)
apply (rule someI2)
apply (auto intro: approx_sym)
done

lemma st_SReal: "x \<in> HFinite ==> st x \<in> Reals"
apply (simp add: st_def)
apply (frule st_part_Ex, safe)
apply (rule someI2)
apply (auto intro: approx_sym)
done

lemma st_HFinite: "x \<in> HFinite ==> st x \<in> HFinite"
by (erule st_SReal [THEN SReal_subset_HFinite [THEN subsetD]])

lemma st_SReal_eq: "x \<in> Reals ==> st x = x"
apply (simp add: st_def)
apply (rule some_equality)
apply (fast intro: SReal_subset_HFinite [THEN subsetD])
apply (blast dest: SReal_approx_iff [THEN iffD1])
done

(* ???should be added to simpset *)
lemma st_hypreal_of_real: "st (hypreal_of_real x) = hypreal_of_real x"
by (rule SReal_hypreal_of_real [THEN st_SReal_eq])

lemma st_eq_approx: "[| x \<in> HFinite; y \<in> HFinite; st x = st y |] ==> x @= y"
by (auto dest!: st_approx_self elim!: approx_trans3)

lemma approx_st_eq: 
  assumes "x \<in> HFinite" and "y \<in> HFinite" and "x @= y" 
  shows "st x = st y"
proof -
  have "st x @= x" "st y @= y" "st x \<in> Reals" "st y \<in> Reals"
    by (simp_all add: st_approx_self st_SReal prems) 
  with prems show ?thesis 
    by (fast elim: approx_trans approx_trans2 SReal_approx_iff [THEN iffD1])
qed

lemma st_eq_approx_iff:
     "[| x \<in> HFinite; y \<in> HFinite|]
                   ==> (x @= y) = (st x = st y)"
by (blast intro: approx_st_eq st_eq_approx)

lemma st_Infinitesimal_add_SReal:
     "[| x \<in> Reals; e \<in> Infinitesimal |] ==> st(x + e) = x"
apply (frule st_SReal_eq [THEN subst])
prefer 2 apply assumption
apply (frule SReal_subset_HFinite [THEN subsetD])
apply (frule Infinitesimal_subset_HFinite [THEN subsetD])
apply (drule st_SReal_eq)
apply (rule approx_st_eq)
apply (auto intro: HFinite_add simp add: Infinitesimal_add_approx_self [THEN approx_sym])
done

lemma st_Infinitesimal_add_SReal2:
     "[| x \<in> Reals; e \<in> Infinitesimal |] ==> st(e + x) = x"
apply (rule hypreal_add_commute [THEN subst])
apply (blast intro!: st_Infinitesimal_add_SReal)
done

lemma HFinite_st_Infinitesimal_add:
     "x \<in> HFinite ==> \<exists>e \<in> Infinitesimal. x = st(x) + e"
by (blast dest!: st_approx_self [THEN approx_sym] bex_Infinitesimal_iff2 [THEN iffD2])

lemma st_add: 
  assumes x: "x \<in> HFinite" and y: "y \<in> HFinite"
  shows "st (x + y) = st(x) + st(y)"
proof -
  from HFinite_st_Infinitesimal_add [OF x]
  obtain ex where ex: "ex \<in> Infinitesimal" "st x + ex = x" 
    by (blast intro: sym)
  from HFinite_st_Infinitesimal_add [OF y]
  obtain ey where ey: "ey \<in> Infinitesimal" "st y + ey = y" 
    by (blast intro: sym)
  have "st (x + y) = st ((st x + ex) + (st y + ey))"
    by (simp add: ex ey) 
  also have "... = st ((ex + ey) + (st x + st y))" by (simp add: add_ac)
  also have "... = st x + st y" 
    by (simp add: prems st_SReal SReal_add Infinitesimal_add 
                  st_Infinitesimal_add_SReal2) 
  finally show ?thesis .
qed

lemma st_number_of: "st (number_of w) = number_of w"
by (rule SReal_number_of [THEN st_SReal_eq])
declare st_number_of [simp]

(*the theorem above for the special cases of zero and one*)
lemma [simp]: "st 0 = 0" "st 1 = 1"
by (simp_all add: st_SReal_eq)

lemma st_minus: assumes "y \<in> HFinite" shows "st(-y) = -st(y)"
proof -
  have "st (- y) + st y = 0"
   by (simp add: prems st_add [symmetric] HFinite_minus_iff) 
  thus ?thesis by arith
qed

lemma st_diff: "[| x \<in> HFinite; y \<in> HFinite |] ==> st (x-y) = st(x) - st(y)"
apply (simp add: hypreal_diff_def)
apply (frule_tac y1 = y in st_minus [symmetric])
apply (drule_tac x1 = y in HFinite_minus_iff [THEN iffD2])
apply (simp (no_asm_simp) add: st_add)
done

(* lemma *)
lemma lemma_st_mult:
     "[| x \<in> HFinite; y \<in> HFinite; e \<in> Infinitesimal; ea \<in> Infinitesimal |]
      ==> e*y + x*ea + e*ea \<in> Infinitesimal"
apply (frule_tac x = e and y = y in Infinitesimal_HFinite_mult)
apply (frule_tac [2] x = ea and y = x in Infinitesimal_HFinite_mult)
apply (drule_tac [3] Infinitesimal_mult)
apply (auto intro: Infinitesimal_add simp add: add_ac mult_ac)
done

lemma st_mult: "[| x \<in> HFinite; y \<in> HFinite |] ==> st (x * y) = st(x) * st(y)"
apply (frule HFinite_st_Infinitesimal_add)
apply (frule_tac x = y in HFinite_st_Infinitesimal_add, safe)
apply (subgoal_tac "st (x * y) = st ((st x + e) * (st y + ea))")
apply (drule_tac [2] sym, drule_tac [2] sym)
 prefer 2 apply simp 
apply (erule_tac V = "x = st x + e" in thin_rl)
apply (erule_tac V = "y = st y + ea" in thin_rl)
apply (simp add: left_distrib right_distrib)
apply (drule st_SReal)+
apply (simp (no_asm_use) add: hypreal_add_assoc)
apply (rule st_Infinitesimal_add_SReal)
apply (blast intro!: SReal_mult)
apply (drule SReal_subset_HFinite [THEN subsetD])+
apply (rule hypreal_add_assoc [THEN subst])
apply (blast intro!: lemma_st_mult)
done

lemma st_Infinitesimal: "x \<in> Infinitesimal ==> st x = 0"
apply (subst numeral_0_eq_0 [symmetric])
apply (rule st_number_of [THEN subst])
apply (rule approx_st_eq)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mem_infmal_iff [symmetric])
done

lemma st_not_Infinitesimal: "st(x) \<noteq> 0 ==> x \<notin> Infinitesimal"
by (fast intro: st_Infinitesimal)

lemma st_inverse:
     "[| x \<in> HFinite; st x \<noteq> 0 |]
      ==> st(inverse x) = inverse (st x)"
apply (rule_tac c1 = "st x" in hypreal_mult_left_cancel [THEN iffD1])
apply (auto simp add: st_mult [symmetric] st_not_Infinitesimal HFinite_inverse)
apply (subst hypreal_mult_inverse, auto)
done

lemma st_divide:
     "[| x \<in> HFinite; y \<in> HFinite; st y \<noteq> 0 |]
      ==> st(x/y) = (st x) / (st y)"
apply (auto simp add: hypreal_divide_def st_mult st_not_Infinitesimal HFinite_inverse st_inverse)
done
declare st_divide [simp]

lemma st_idempotent: "x \<in> HFinite ==> st(st(x)) = st(x)"
by (blast intro: st_HFinite st_approx_self approx_st_eq)
declare st_idempotent [simp]

lemma Infinitesimal_add_st_less:
     "[| x \<in> HFinite; y \<in> HFinite; u \<in> Infinitesimal; st x < st y |] 
      ==> st x + u < st y"
apply (drule st_SReal)+
apply (auto intro!: Infinitesimal_add_hypreal_of_real_less simp add: SReal_iff)
done

lemma Infinitesimal_add_st_le_cancel:
     "[| x \<in> HFinite; y \<in> HFinite;
         u \<in> Infinitesimal; st x \<le> st y + u
      |] ==> st x \<le> st y"
apply (simp add: linorder_not_less [symmetric])
apply (auto dest: Infinitesimal_add_st_less)
done

lemma st_le: "[| x \<in> HFinite; y \<in> HFinite; x \<le> y |] ==> st(x) \<le> st(y)"
apply (frule HFinite_st_Infinitesimal_add)
apply (rotate_tac 1)
apply (frule HFinite_st_Infinitesimal_add, safe)
apply (rule Infinitesimal_add_st_le_cancel)
apply (rule_tac [3] x = ea and y = e in Infinitesimal_diff)
apply (auto simp add: hypreal_add_assoc [symmetric])
done

lemma st_zero_le: "[| 0 \<le> x;  x \<in> HFinite |] ==> 0 \<le> st x"
apply (subst numeral_0_eq_0 [symmetric])
apply (rule st_number_of [THEN subst])
apply (rule st_le, auto)
done

lemma st_zero_ge: "[| x \<le> 0;  x \<in> HFinite |] ==> st x \<le> 0"
apply (subst numeral_0_eq_0 [symmetric])
apply (rule st_number_of [THEN subst])
apply (rule st_le, auto)
done

lemma st_hrabs: "x \<in> HFinite ==> abs(st x) = st(abs x)"
apply (simp add: linorder_not_le st_zero_le abs_if st_minus
   linorder_not_less)
apply (auto dest!: st_zero_ge [OF order_less_imp_le]) 
done



subsection{*Alternative Definitions for @{term HFinite} using Free Ultrafilter*}

lemma FreeUltrafilterNat_Rep_hypreal:
     "[| X \<in> Rep_hypreal x; Y \<in> Rep_hypreal x |]
      ==> {n. X n = Y n} \<in> FreeUltrafilterNat"
by (rule_tac z = x in eq_Abs_hypreal, auto, ultra)

lemma HFinite_FreeUltrafilterNat:
    "x \<in> HFinite 
     ==> \<exists>X \<in> Rep_hypreal x. \<exists>u. {n. abs (X n) < u} \<in> FreeUltrafilterNat"
apply (cases x)
apply (auto simp add: HFinite_def abs_less_iff minus_less_iff [of x] 
              hypreal_less SReal_iff hypreal_minus hypreal_of_real_def)
apply (rule_tac x=x in bexI) 
apply (rule_tac x=y in exI, auto, ultra)
done

lemma FreeUltrafilterNat_HFinite:
     "\<exists>X \<in> Rep_hypreal x.
       \<exists>u. {n. abs (X n) < u} \<in> FreeUltrafilterNat
       ==>  x \<in> HFinite"
apply (cases x)
apply (auto simp add: HFinite_def abs_less_iff minus_less_iff [of x])
apply (rule_tac x = "hypreal_of_real u" in bexI)
apply (auto simp add: hypreal_less SReal_iff hypreal_minus hypreal_of_real_def, ultra+)
done

lemma HFinite_FreeUltrafilterNat_iff:
     "(x \<in> HFinite) = (\<exists>X \<in> Rep_hypreal x.
           \<exists>u. {n. abs (X n) < u} \<in> FreeUltrafilterNat)"
apply (blast intro!: HFinite_FreeUltrafilterNat FreeUltrafilterNat_HFinite)
done


subsection{*Alternative Definitions for @{term HInfinite} using Free Ultrafilter*}

lemma lemma_Compl_eq: "- {n. (u::real) < abs (xa n)} = {n. abs (xa n) \<le> u}"
by auto

lemma lemma_Compl_eq2: "- {n. abs (xa n) < (u::real)} = {n. u \<le> abs (xa n)}"
by auto

lemma lemma_Int_eq1:
     "{n. abs (xa n) \<le> (u::real)} Int {n. u \<le> abs (xa n)}
          = {n. abs(xa n) = u}"
apply auto
done

lemma lemma_FreeUltrafilterNat_one:
     "{n. abs (xa n) = u} \<le> {n. abs (xa n) < u + (1::real)}"
by auto

(*-------------------------------------
  Exclude this type of sets from free
  ultrafilter for Infinite numbers!
 -------------------------------------*)
lemma FreeUltrafilterNat_const_Finite:
     "[| xa: Rep_hypreal x;
                  {n. abs (xa n) = u} \<in> FreeUltrafilterNat
               |] ==> x \<in> HFinite"
apply (rule FreeUltrafilterNat_HFinite)
apply (rule_tac x = xa in bexI)
apply (rule_tac x = "u + 1" in exI)
apply (ultra, assumption)
done

lemma HInfinite_FreeUltrafilterNat:
     "x \<in> HInfinite ==> \<exists>X \<in> Rep_hypreal x.
           \<forall>u. {n. u < abs (X n)} \<in> FreeUltrafilterNat"
apply (frule HInfinite_HFinite_iff [THEN iffD1])
apply (cut_tac x = x in Rep_hypreal_nonempty)
apply (auto simp del: Rep_hypreal_nonempty simp add: HFinite_FreeUltrafilterNat_iff Bex_def)
apply (drule spec)+
apply auto
apply (drule_tac x = u in spec)
apply (drule FreeUltrafilterNat_Compl_mem)+
apply (drule FreeUltrafilterNat_Int, assumption)
apply (simp add: lemma_Compl_eq lemma_Compl_eq2 lemma_Int_eq1)
apply (auto dest: FreeUltrafilterNat_const_Finite simp
      add: HInfinite_HFinite_iff [THEN iffD1])
done

lemma lemma_Int_HI:
     "{n. abs (Xa n) < u} Int {n. X n = Xa n} \<subseteq> {n. abs (X n) < (u::real)}"
by auto

lemma lemma_Int_HIa: "{n. u < abs (X n)} Int {n. abs (X n) < (u::real)} = {}"
by (auto intro: order_less_asym)

lemma FreeUltrafilterNat_HInfinite:
     "\<exists>X \<in> Rep_hypreal x. \<forall>u.
               {n. u < abs (X n)} \<in> FreeUltrafilterNat
               ==>  x \<in> HInfinite"
apply (rule HInfinite_HFinite_iff [THEN iffD2])
apply (safe, drule HFinite_FreeUltrafilterNat, auto)
apply (drule_tac x = u in spec)
apply (drule FreeUltrafilterNat_Rep_hypreal, assumption)
apply (drule_tac Y = "{n. X n = Xa n}" in FreeUltrafilterNat_Int, simp) 
apply (drule lemma_Int_HI [THEN [2] FreeUltrafilterNat_subset])
apply (drule_tac Y = "{n. abs (X n) < u}" in FreeUltrafilterNat_Int)
apply (auto simp add: lemma_Int_HIa FreeUltrafilterNat_empty)
done

lemma HInfinite_FreeUltrafilterNat_iff:
     "(x \<in> HInfinite) = (\<exists>X \<in> Rep_hypreal x.
           \<forall>u. {n. u < abs (X n)} \<in> FreeUltrafilterNat)"
by (blast intro!: HInfinite_FreeUltrafilterNat FreeUltrafilterNat_HInfinite)


subsection{*Alternative Definitions for @{term Infinitesimal} using Free Ultrafilter*}

lemma Infinitesimal_FreeUltrafilterNat:
          "x \<in> Infinitesimal ==> \<exists>X \<in> Rep_hypreal x.
           \<forall>u. 0 < u --> {n. abs (X n) < u} \<in> FreeUltrafilterNat"
apply (simp add: Infinitesimal_def)
apply (auto simp add: abs_less_iff minus_less_iff [of x])
apply (cases x)
apply (auto, rule bexI [OF _ lemma_hyprel_refl], safe)
apply (drule hypreal_of_real_less_iff [THEN iffD2])
apply (drule_tac x = "hypreal_of_real u" in bspec, auto)
apply (auto simp add: hypreal_less hypreal_minus hypreal_of_real_def, ultra)
done

lemma FreeUltrafilterNat_Infinitesimal:
     "\<exists>X \<in> Rep_hypreal x.
            \<forall>u. 0 < u --> {n. abs (X n) < u} \<in> FreeUltrafilterNat
      ==> x \<in> Infinitesimal"
apply (simp add: Infinitesimal_def)
apply (cases x)
apply (auto simp add: abs_less_iff abs_interval_iff minus_less_iff [of x])
apply (auto simp add: SReal_iff)
apply (drule_tac [!] x=y in spec) 
apply (auto simp add: hypreal_less hypreal_minus hypreal_of_real_def, ultra+)
done

lemma Infinitesimal_FreeUltrafilterNat_iff:
     "(x \<in> Infinitesimal) = (\<exists>X \<in> Rep_hypreal x.
           \<forall>u. 0 < u --> {n. abs (X n) < u} \<in> FreeUltrafilterNat)"
apply (blast intro!: Infinitesimal_FreeUltrafilterNat FreeUltrafilterNat_Infinitesimal)
done

(*------------------------------------------------------------------------
         Infinitesimals as smaller than 1/n for all n::nat (> 0)
 ------------------------------------------------------------------------*)

lemma lemma_Infinitesimal:
     "(\<forall>r. 0 < r --> x < r) = (\<forall>n. x < inverse(real (Suc n)))"
apply (auto simp add: real_of_nat_Suc_gt_zero)
apply (blast dest!: reals_Archimedean intro: order_less_trans)
done

lemma of_nat_in_Reals [simp]: "(of_nat n::hypreal) \<in> \<real>"
apply (induct n)
apply (simp_all add: SReal_add)
done 
 
lemma lemma_Infinitesimal2:
     "(\<forall>r \<in> Reals. 0 < r --> x < r) =
      (\<forall>n. x < inverse(hypreal_of_nat (Suc n)))"
apply safe
apply (drule_tac x = "inverse (hypreal_of_real (real (Suc n))) " in bspec)
apply (simp (no_asm_use) add: SReal_inverse)
apply (rule real_of_nat_Suc_gt_zero [THEN positive_imp_inverse_positive, THEN hypreal_of_real_less_iff [THEN iffD2], THEN [2] impE])
prefer 2 apply assumption
apply (simp add: real_of_nat_Suc_gt_zero hypreal_of_nat_eq)
apply (auto dest!: reals_Archimedean simp add: SReal_iff)
apply (drule hypreal_of_real_less_iff [THEN iffD2])
apply (simp add: real_of_nat_Suc_gt_zero hypreal_of_nat_eq)
apply (blast intro: order_less_trans)
done


lemma Infinitesimal_hypreal_of_nat_iff:
     "Infinitesimal = {x. \<forall>n. abs x < inverse (hypreal_of_nat (Suc n))}"
apply (simp add: Infinitesimal_def)
apply (auto simp add: lemma_Infinitesimal2)
done


(*-------------------------------------------------------------------------
       Proof that omega is an infinite number and
       hence that epsilon is an infinitesimal number.
 -------------------------------------------------------------------------*)
lemma Suc_Un_eq: "{n. n < Suc m} = {n. n < m} Un {n. n = m}"
by (auto simp add: less_Suc_eq)

(*-------------------------------------------
  Prove that any segment is finite and
  hence cannot belong to FreeUltrafilterNat
 -------------------------------------------*)
lemma finite_nat_segment: "finite {n::nat. n < m}"
apply (induct_tac "m")
apply (auto simp add: Suc_Un_eq)
done

lemma finite_real_of_nat_segment: "finite {n::nat. real n < real (m::nat)}"
by (auto intro: finite_nat_segment)

lemma finite_real_of_nat_less_real: "finite {n::nat. real n < u}"
apply (cut_tac x = u in reals_Archimedean2, safe)
apply (rule finite_real_of_nat_segment [THEN [2] finite_subset])
apply (auto dest: order_less_trans)
done

lemma lemma_real_le_Un_eq:
     "{n. f n \<le> u} = {n. f n < u} Un {n. u = (f n :: real)}"
by (auto dest: order_le_imp_less_or_eq simp add: order_less_imp_le)

lemma finite_real_of_nat_le_real: "finite {n::nat. real n \<le> u}"
by (auto simp add: lemma_real_le_Un_eq lemma_finite_omega_set finite_real_of_nat_less_real)

lemma finite_rabs_real_of_nat_le_real: "finite {n::nat. abs(real n) \<le> u}"
apply (simp (no_asm) add: real_of_nat_Suc_gt_zero finite_real_of_nat_le_real)
done

lemma rabs_real_of_nat_le_real_FreeUltrafilterNat:
     "{n. abs(real n) \<le> u} \<notin> FreeUltrafilterNat"
by (blast intro!: FreeUltrafilterNat_finite finite_rabs_real_of_nat_le_real)

lemma FreeUltrafilterNat_nat_gt_real: "{n. u < real n} \<in> FreeUltrafilterNat"
apply (rule ccontr, drule FreeUltrafilterNat_Compl_mem)
apply (subgoal_tac "- {n::nat. u < real n} = {n. real n \<le> u}")
prefer 2 apply force
apply (simp add: finite_real_of_nat_le_real [THEN FreeUltrafilterNat_finite])
done

(*--------------------------------------------------------------
 The complement of {n. abs(real n) \<le> u} =
 {n. u < abs (real n)} is in FreeUltrafilterNat
 by property of (free) ultrafilters
 --------------------------------------------------------------*)

lemma Compl_real_le_eq: "- {n::nat. real n \<le> u} = {n. u < real n}"
by (auto dest!: order_le_less_trans simp add: linorder_not_le)

(*-----------------------------------------------
       Omega is a member of HInfinite
 -----------------------------------------------*)

lemma hypreal_omega: "hyprel``{%n::nat. real (Suc n)} \<in> hypreal"
by auto

lemma FreeUltrafilterNat_omega: "{n. u < real n} \<in> FreeUltrafilterNat"
apply (cut_tac u = u in rabs_real_of_nat_le_real_FreeUltrafilterNat)
apply (auto dest: FreeUltrafilterNat_Compl_mem simp add: Compl_real_le_eq)
done

lemma HInfinite_omega: "omega: HInfinite"
apply (simp add: omega_def)
apply (auto intro!: FreeUltrafilterNat_HInfinite)
apply (rule bexI)
apply (rule_tac [2] lemma_hyprel_refl, auto)
apply (simp (no_asm) add: real_of_nat_Suc diff_less_eq [symmetric] FreeUltrafilterNat_omega)
done
declare HInfinite_omega [simp]

(*-----------------------------------------------
       Epsilon is a member of Infinitesimal
 -----------------------------------------------*)

lemma Infinitesimal_epsilon: "epsilon \<in> Infinitesimal"
by (auto intro!: HInfinite_inverse_Infinitesimal HInfinite_omega simp add: hypreal_epsilon_inverse_omega)
declare Infinitesimal_epsilon [simp]

lemma HFinite_epsilon: "epsilon \<in> HFinite"
by (auto intro: Infinitesimal_subset_HFinite [THEN subsetD])
declare HFinite_epsilon [simp]

lemma epsilon_approx_zero: "epsilon @= 0"
apply (simp (no_asm) add: mem_infmal_iff [symmetric])
done
declare epsilon_approx_zero [simp]

(*------------------------------------------------------------------------
  Needed for proof that we define a hyperreal [<X(n)] @= hypreal_of_real a given
  that \<forall>n. |X n - a| < 1/n. Used in proof of NSLIM => LIM.
 -----------------------------------------------------------------------*)

lemma real_of_nat_less_inverse_iff:
     "0 < u  ==> (u < inverse (real(Suc n))) = (real(Suc n) < inverse u)"
apply (simp add: inverse_eq_divide)
apply (subst pos_less_divide_eq, assumption)
apply (subst pos_less_divide_eq)
 apply (simp add: real_of_nat_Suc_gt_zero)
apply (simp add: real_mult_commute)
done

lemma finite_inverse_real_of_posnat_gt_real:
     "0 < u ==> finite {n. u < inverse(real(Suc n))}"
apply (simp (no_asm_simp) add: real_of_nat_less_inverse_iff)
apply (simp (no_asm_simp) add: real_of_nat_Suc less_diff_eq [symmetric])
apply (rule finite_real_of_nat_less_real)
done

lemma lemma_real_le_Un_eq2:
     "{n. u \<le> inverse(real(Suc n))} =
     {n. u < inverse(real(Suc n))} Un {n. u = inverse(real(Suc n))}"
apply (auto dest: order_le_imp_less_or_eq simp add: order_less_imp_le)
done

lemma real_of_nat_inverse_le_iff:
     "(inverse (real(Suc n)) \<le> r) = (1 \<le> r * real(Suc n))"
apply (simp (no_asm) add: linorder_not_less [symmetric])
apply (simp (no_asm) add: inverse_eq_divide)
apply (subst pos_less_divide_eq)
apply (simp (no_asm) add: real_of_nat_Suc_gt_zero)
apply (simp (no_asm) add: real_mult_commute)
done

lemma real_of_nat_inverse_eq_iff:
     "(u = inverse (real(Suc n))) = (real(Suc n) = inverse u)"
by (auto simp add: inverse_inverse_eq real_of_nat_Suc_gt_zero real_not_refl2 [THEN not_sym])

lemma lemma_finite_omega_set2: "finite {n::nat. u = inverse(real(Suc n))}"
apply (simp (no_asm_simp) add: real_of_nat_inverse_eq_iff)
apply (cut_tac x = "inverse u - 1" in lemma_finite_omega_set)
apply (simp add: real_of_nat_Suc diff_eq_eq [symmetric] eq_commute)
done

lemma finite_inverse_real_of_posnat_ge_real:
     "0 < u ==> finite {n. u \<le> inverse(real(Suc n))}"
by (auto simp add: lemma_real_le_Un_eq2 lemma_finite_omega_set2 finite_inverse_real_of_posnat_gt_real)

lemma inverse_real_of_posnat_ge_real_FreeUltrafilterNat:
     "0 < u ==> {n. u \<le> inverse(real(Suc n))} \<notin> FreeUltrafilterNat"
by (blast intro!: FreeUltrafilterNat_finite finite_inverse_real_of_posnat_ge_real)

(*--------------------------------------------------------------
    The complement of  {n. u \<le> inverse(real(Suc n))} =
    {n. inverse(real(Suc n)) < u} is in FreeUltrafilterNat
    by property of (free) ultrafilters
 --------------------------------------------------------------*)
lemma Compl_le_inverse_eq:
     "- {n. u \<le> inverse(real(Suc n))} =
      {n. inverse(real(Suc n)) < u}"
apply (auto dest!: order_le_less_trans simp add: linorder_not_le)
done

lemma FreeUltrafilterNat_inverse_real_of_posnat:
     "0 < u ==>
      {n. inverse(real(Suc n)) < u} \<in> FreeUltrafilterNat"
apply (cut_tac u = u in inverse_real_of_posnat_ge_real_FreeUltrafilterNat)
apply (auto dest: FreeUltrafilterNat_Compl_mem simp add: Compl_le_inverse_eq)
done

text{* Example where we get a hyperreal from a real sequence
      for which a particular property holds. The theorem is
      used in proofs about equivalence of nonstandard and
      standard neighbourhoods. Also used for equivalence of
      nonstandard ans standard definitions of pointwise
      limit.*}

(*-----------------------------------------------------
    |X(n) - x| < 1/n ==> [<X n>] - hypreal_of_real x| \<in> Infinitesimal
 -----------------------------------------------------*)
lemma real_seq_to_hypreal_Infinitesimal:
     "\<forall>n. abs(X n + -x) < inverse(real(Suc n))
     ==> Abs_hypreal(hyprel``{X}) + -hypreal_of_real x \<in> Infinitesimal"
apply (auto intro!: bexI dest: FreeUltrafilterNat_inverse_real_of_posnat FreeUltrafilterNat_all FreeUltrafilterNat_Int intro: order_less_trans FreeUltrafilterNat_subset simp add: hypreal_minus hypreal_of_real_def hypreal_add Infinitesimal_FreeUltrafilterNat_iff hypreal_inverse)
done

lemma real_seq_to_hypreal_approx:
     "\<forall>n. abs(X n + -x) < inverse(real(Suc n))
      ==> Abs_hypreal(hyprel``{X}) @= hypreal_of_real x"
apply (subst approx_minus_iff)
apply (rule mem_infmal_iff [THEN subst])
apply (erule real_seq_to_hypreal_Infinitesimal)
done

lemma real_seq_to_hypreal_approx2:
     "\<forall>n. abs(x + -X n) < inverse(real(Suc n))
               ==> Abs_hypreal(hyprel``{X}) @= hypreal_of_real x"
apply (simp add: abs_minus_add_cancel real_seq_to_hypreal_approx)
done

lemma real_seq_to_hypreal_Infinitesimal2:
     "\<forall>n. abs(X n + -Y n) < inverse(real(Suc n))
      ==> Abs_hypreal(hyprel``{X}) +
          -Abs_hypreal(hyprel``{Y}) \<in> Infinitesimal"
by (auto intro!: bexI
	 dest: FreeUltrafilterNat_inverse_real_of_posnat 
	       FreeUltrafilterNat_all FreeUltrafilterNat_Int
	 intro: order_less_trans FreeUltrafilterNat_subset 
	 simp add: Infinitesimal_FreeUltrafilterNat_iff hypreal_minus 
                   hypreal_add hypreal_inverse)


ML
{*
val Infinitesimal_def = thm"Infinitesimal_def";
val HFinite_def = thm"HFinite_def";
val HInfinite_def = thm"HInfinite_def";
val st_def = thm"st_def";
val monad_def = thm"monad_def";
val galaxy_def = thm"galaxy_def";
val approx_def = thm"approx_def";
val SReal_def = thm"SReal_def";

val Infinitesimal_approx_minus = thm "Infinitesimal_approx_minus";
val approx_monad_iff = thm "approx_monad_iff";
val Infinitesimal_approx = thm "Infinitesimal_approx";
val approx_add = thm "approx_add";
val approx_minus = thm "approx_minus";
val approx_minus2 = thm "approx_minus2";
val approx_minus_cancel = thm "approx_minus_cancel";
val approx_add_minus = thm "approx_add_minus";
val approx_mult1 = thm "approx_mult1";
val approx_mult2 = thm "approx_mult2";
val approx_mult_subst = thm "approx_mult_subst";
val approx_mult_subst2 = thm "approx_mult_subst2";
val approx_mult_subst_SReal = thm "approx_mult_subst_SReal";
val approx_eq_imp = thm "approx_eq_imp";
val Infinitesimal_minus_approx = thm "Infinitesimal_minus_approx";
val bex_Infinitesimal_iff = thm "bex_Infinitesimal_iff";
val bex_Infinitesimal_iff2 = thm "bex_Infinitesimal_iff2";
val Infinitesimal_add_approx = thm "Infinitesimal_add_approx";
val Infinitesimal_add_approx_self = thm "Infinitesimal_add_approx_self";
val Infinitesimal_add_approx_self2 = thm "Infinitesimal_add_approx_self2";
val Infinitesimal_add_minus_approx_self = thm "Infinitesimal_add_minus_approx_self";
val Infinitesimal_add_cancel = thm "Infinitesimal_add_cancel";
val Infinitesimal_add_right_cancel = thm "Infinitesimal_add_right_cancel";
val approx_add_left_cancel = thm "approx_add_left_cancel";
val approx_add_right_cancel = thm "approx_add_right_cancel";
val approx_add_mono1 = thm "approx_add_mono1";
val approx_add_mono2 = thm "approx_add_mono2";
val approx_add_left_iff = thm "approx_add_left_iff";
val approx_add_right_iff = thm "approx_add_right_iff";
val approx_HFinite = thm "approx_HFinite";
val approx_hypreal_of_real_HFinite = thm "approx_hypreal_of_real_HFinite";
val approx_mult_HFinite = thm "approx_mult_HFinite";
val approx_mult_hypreal_of_real = thm "approx_mult_hypreal_of_real";
val approx_SReal_mult_cancel_zero = thm "approx_SReal_mult_cancel_zero";
val approx_mult_SReal1 = thm "approx_mult_SReal1";
val approx_mult_SReal2 = thm "approx_mult_SReal2";
val approx_mult_SReal_zero_cancel_iff = thm "approx_mult_SReal_zero_cancel_iff";
val approx_SReal_mult_cancel = thm "approx_SReal_mult_cancel";
val approx_SReal_mult_cancel_iff1 = thm "approx_SReal_mult_cancel_iff1";
val approx_le_bound = thm "approx_le_bound";
val Infinitesimal_less_SReal = thm "Infinitesimal_less_SReal";
val Infinitesimal_less_SReal2 = thm "Infinitesimal_less_SReal2";
val SReal_not_Infinitesimal = thm "SReal_not_Infinitesimal";
val SReal_minus_not_Infinitesimal = thm "SReal_minus_not_Infinitesimal";
val SReal_Int_Infinitesimal_zero = thm "SReal_Int_Infinitesimal_zero";
val SReal_Infinitesimal_zero = thm "SReal_Infinitesimal_zero";
val SReal_HFinite_diff_Infinitesimal = thm "SReal_HFinite_diff_Infinitesimal";
val hypreal_of_real_HFinite_diff_Infinitesimal = thm "hypreal_of_real_HFinite_diff_Infinitesimal";
val hypreal_of_real_Infinitesimal_iff_0 = thm "hypreal_of_real_Infinitesimal_iff_0";
val number_of_not_Infinitesimal = thm "number_of_not_Infinitesimal";
val one_not_Infinitesimal = thm "one_not_Infinitesimal";
val approx_SReal_not_zero = thm "approx_SReal_not_zero";
val HFinite_diff_Infinitesimal_approx = thm "HFinite_diff_Infinitesimal_approx";
val Infinitesimal_ratio = thm "Infinitesimal_ratio";
val SReal_approx_iff = thm "SReal_approx_iff";
val number_of_approx_iff = thm "number_of_approx_iff";
val hypreal_of_real_approx_iff = thm "hypreal_of_real_approx_iff";
val hypreal_of_real_approx_number_of_iff = thm "hypreal_of_real_approx_number_of_iff";
val approx_unique_real = thm "approx_unique_real";
val hypreal_isLub_unique = thm "hypreal_isLub_unique";
val hypreal_setle_less_trans = thm "hypreal_setle_less_trans";
val hypreal_gt_isUb = thm "hypreal_gt_isUb";
val st_part_Ex = thm "st_part_Ex";
val st_part_Ex1 = thm "st_part_Ex1";
val HFinite_Int_HInfinite_empty = thm "HFinite_Int_HInfinite_empty";
val HFinite_not_HInfinite = thm "HFinite_not_HInfinite";
val not_HFinite_HInfinite = thm "not_HFinite_HInfinite";
val HInfinite_HFinite_disj = thm "HInfinite_HFinite_disj";
val HInfinite_HFinite_iff = thm "HInfinite_HFinite_iff";
val HFinite_HInfinite_iff = thm "HFinite_HInfinite_iff";
val HInfinite_diff_HFinite_Infinitesimal_disj = thm "HInfinite_diff_HFinite_Infinitesimal_disj";
val HFinite_inverse = thm "HFinite_inverse";
val HFinite_inverse2 = thm "HFinite_inverse2";
val Infinitesimal_inverse_HFinite = thm "Infinitesimal_inverse_HFinite";
val HFinite_not_Infinitesimal_inverse = thm "HFinite_not_Infinitesimal_inverse";
val approx_inverse = thm "approx_inverse";
val hypreal_of_real_approx_inverse = thm "hypreal_of_real_approx_inverse";
val inverse_add_Infinitesimal_approx = thm "inverse_add_Infinitesimal_approx";
val inverse_add_Infinitesimal_approx2 = thm "inverse_add_Infinitesimal_approx2";
val inverse_add_Infinitesimal_approx_Infinitesimal = thm "inverse_add_Infinitesimal_approx_Infinitesimal";
val Infinitesimal_square_iff = thm "Infinitesimal_square_iff";
val HFinite_square_iff = thm "HFinite_square_iff";
val HInfinite_square_iff = thm "HInfinite_square_iff";
val approx_HFinite_mult_cancel = thm "approx_HFinite_mult_cancel";
val approx_HFinite_mult_cancel_iff1 = thm "approx_HFinite_mult_cancel_iff1";
val approx_hrabs_disj = thm "approx_hrabs_disj";
val monad_hrabs_Un_subset = thm "monad_hrabs_Un_subset";
val Infinitesimal_monad_eq = thm "Infinitesimal_monad_eq";
val mem_monad_iff = thm "mem_monad_iff";
val Infinitesimal_monad_zero_iff = thm "Infinitesimal_monad_zero_iff";
val monad_zero_minus_iff = thm "monad_zero_minus_iff";
val monad_zero_hrabs_iff = thm "monad_zero_hrabs_iff";
val mem_monad_self = thm "mem_monad_self";
val approx_subset_monad = thm "approx_subset_monad";
val approx_subset_monad2 = thm "approx_subset_monad2";
val mem_monad_approx = thm "mem_monad_approx";
val approx_mem_monad = thm "approx_mem_monad";
val approx_mem_monad2 = thm "approx_mem_monad2";
val approx_mem_monad_zero = thm "approx_mem_monad_zero";
val Infinitesimal_approx_hrabs = thm "Infinitesimal_approx_hrabs";
val less_Infinitesimal_less = thm "less_Infinitesimal_less";
val Ball_mem_monad_gt_zero = thm "Ball_mem_monad_gt_zero";
val Ball_mem_monad_less_zero = thm "Ball_mem_monad_less_zero";
val approx_hrabs1 = thm "approx_hrabs1";
val approx_hrabs2 = thm "approx_hrabs2";
val approx_hrabs = thm "approx_hrabs";
val approx_hrabs_zero_cancel = thm "approx_hrabs_zero_cancel";
val approx_hrabs_add_Infinitesimal = thm "approx_hrabs_add_Infinitesimal";
val approx_hrabs_add_minus_Infinitesimal = thm "approx_hrabs_add_minus_Infinitesimal";
val hrabs_add_Infinitesimal_cancel = thm "hrabs_add_Infinitesimal_cancel";
val hrabs_add_minus_Infinitesimal_cancel = thm "hrabs_add_minus_Infinitesimal_cancel";
val hypreal_less_minus_iff = thm "hypreal_less_minus_iff";
val Infinitesimal_add_hypreal_of_real_less = thm "Infinitesimal_add_hypreal_of_real_less";
val Infinitesimal_add_hrabs_hypreal_of_real_less = thm "Infinitesimal_add_hrabs_hypreal_of_real_less";
val Infinitesimal_add_hrabs_hypreal_of_real_less2 = thm "Infinitesimal_add_hrabs_hypreal_of_real_less2";
val hypreal_of_real_le_add_Infininitesimal_cancel2 = thm"hypreal_of_real_le_add_Infininitesimal_cancel2";
val hypreal_of_real_less_Infinitesimal_le_zero = thm "hypreal_of_real_less_Infinitesimal_le_zero";
val Infinitesimal_add_not_zero = thm "Infinitesimal_add_not_zero";
val Infinitesimal_square_cancel = thm "Infinitesimal_square_cancel";
val HFinite_square_cancel = thm "HFinite_square_cancel";
val Infinitesimal_square_cancel2 = thm "Infinitesimal_square_cancel2";
val HFinite_square_cancel2 = thm "HFinite_square_cancel2";
val Infinitesimal_sum_square_cancel = thm "Infinitesimal_sum_square_cancel";
val HFinite_sum_square_cancel = thm "HFinite_sum_square_cancel";
val Infinitesimal_sum_square_cancel2 = thm "Infinitesimal_sum_square_cancel2";
val HFinite_sum_square_cancel2 = thm "HFinite_sum_square_cancel2";
val Infinitesimal_sum_square_cancel3 = thm "Infinitesimal_sum_square_cancel3";
val HFinite_sum_square_cancel3 = thm "HFinite_sum_square_cancel3";
val monad_hrabs_less = thm "monad_hrabs_less";
val mem_monad_SReal_HFinite = thm "mem_monad_SReal_HFinite";
val st_approx_self = thm "st_approx_self";
val st_SReal = thm "st_SReal";
val st_HFinite = thm "st_HFinite";
val st_SReal_eq = thm "st_SReal_eq";
val st_hypreal_of_real = thm "st_hypreal_of_real";
val st_eq_approx = thm "st_eq_approx";
val approx_st_eq = thm "approx_st_eq";
val st_eq_approx_iff = thm "st_eq_approx_iff";
val st_Infinitesimal_add_SReal = thm "st_Infinitesimal_add_SReal";
val st_Infinitesimal_add_SReal2 = thm "st_Infinitesimal_add_SReal2";
val HFinite_st_Infinitesimal_add = thm "HFinite_st_Infinitesimal_add";
val st_add = thm "st_add";
val st_number_of = thm "st_number_of";
val st_minus = thm "st_minus";
val st_diff = thm "st_diff";
val st_mult = thm "st_mult";
val st_Infinitesimal = thm "st_Infinitesimal";
val st_not_Infinitesimal = thm "st_not_Infinitesimal";
val st_inverse = thm "st_inverse";
val st_divide = thm "st_divide";
val st_idempotent = thm "st_idempotent";
val Infinitesimal_add_st_less = thm "Infinitesimal_add_st_less";
val Infinitesimal_add_st_le_cancel = thm "Infinitesimal_add_st_le_cancel";
val st_le = thm "st_le";
val st_zero_le = thm "st_zero_le";
val st_zero_ge = thm "st_zero_ge";
val st_hrabs = thm "st_hrabs";
val FreeUltrafilterNat_HFinite = thm "FreeUltrafilterNat_HFinite";
val HFinite_FreeUltrafilterNat_iff = thm "HFinite_FreeUltrafilterNat_iff";
val FreeUltrafilterNat_const_Finite = thm "FreeUltrafilterNat_const_Finite";
val FreeUltrafilterNat_HInfinite = thm "FreeUltrafilterNat_HInfinite";
val HInfinite_FreeUltrafilterNat_iff = thm "HInfinite_FreeUltrafilterNat_iff";
val Infinitesimal_FreeUltrafilterNat = thm "Infinitesimal_FreeUltrafilterNat";
val FreeUltrafilterNat_Infinitesimal = thm "FreeUltrafilterNat_Infinitesimal";
val Infinitesimal_FreeUltrafilterNat_iff = thm "Infinitesimal_FreeUltrafilterNat_iff";
val Infinitesimal_hypreal_of_nat_iff = thm "Infinitesimal_hypreal_of_nat_iff";
val Suc_Un_eq = thm "Suc_Un_eq";
val finite_nat_segment = thm "finite_nat_segment";
val finite_real_of_nat_segment = thm "finite_real_of_nat_segment";
val finite_real_of_nat_less_real = thm "finite_real_of_nat_less_real";
val finite_real_of_nat_le_real = thm "finite_real_of_nat_le_real";
val finite_rabs_real_of_nat_le_real = thm "finite_rabs_real_of_nat_le_real";
val rabs_real_of_nat_le_real_FreeUltrafilterNat = thm "rabs_real_of_nat_le_real_FreeUltrafilterNat";
val FreeUltrafilterNat_nat_gt_real = thm "FreeUltrafilterNat_nat_gt_real";
val hypreal_omega = thm "hypreal_omega";
val FreeUltrafilterNat_omega = thm "FreeUltrafilterNat_omega";
val HInfinite_omega = thm "HInfinite_omega";
val Infinitesimal_epsilon = thm "Infinitesimal_epsilon";
val HFinite_epsilon = thm "HFinite_epsilon";
val epsilon_approx_zero = thm "epsilon_approx_zero";
val real_of_nat_less_inverse_iff = thm "real_of_nat_less_inverse_iff";
val finite_inverse_real_of_posnat_gt_real = thm "finite_inverse_real_of_posnat_gt_real";
val real_of_nat_inverse_le_iff = thm "real_of_nat_inverse_le_iff";
val real_of_nat_inverse_eq_iff = thm "real_of_nat_inverse_eq_iff";
val finite_inverse_real_of_posnat_ge_real = thm "finite_inverse_real_of_posnat_ge_real";
val inverse_real_of_posnat_ge_real_FreeUltrafilterNat = thm "inverse_real_of_posnat_ge_real_FreeUltrafilterNat";
val FreeUltrafilterNat_inverse_real_of_posnat = thm "FreeUltrafilterNat_inverse_real_of_posnat";
val real_seq_to_hypreal_Infinitesimal = thm "real_seq_to_hypreal_Infinitesimal";
val real_seq_to_hypreal_approx = thm "real_seq_to_hypreal_approx";
val real_seq_to_hypreal_approx2 = thm "real_seq_to_hypreal_approx2";
val real_seq_to_hypreal_Infinitesimal2 = thm "real_seq_to_hypreal_Infinitesimal2";
val HInfinite_HFinite_add = thm "HInfinite_HFinite_add";
val HInfinite_ge_HInfinite = thm "HInfinite_ge_HInfinite";
val Infinitesimal_inverse_HInfinite = thm "Infinitesimal_inverse_HInfinite";
val HInfinite_HFinite_not_Infinitesimal_mult = thm "HInfinite_HFinite_not_Infinitesimal_mult";
val HInfinite_HFinite_not_Infinitesimal_mult2 = thm "HInfinite_HFinite_not_Infinitesimal_mult2";
val HInfinite_gt_SReal = thm "HInfinite_gt_SReal";
val HInfinite_gt_zero_gt_one = thm "HInfinite_gt_zero_gt_one";
val not_HInfinite_one = thm "not_HInfinite_one";
*}

end

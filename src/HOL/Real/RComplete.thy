(*  Title       : RComplete.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Completeness theorems for positive
                  reals and reals 
*) 

header{*Completeness Theorems for Positive Reals and Reals.*}

theory RComplete = Lubs + RealDef:

lemma real_sum_of_halves: "x/2 + x/2 = (x::real)"
by simp


subsection{*Completeness of Reals by Supremum Property of type @{typ preal}*} 

 (*a few lemmas*)
lemma real_sup_lemma1:
     "\<forall>x \<in> P. 0 < x ==>   
      ((\<exists>x \<in> P. y < x) = (\<exists>X. real_of_preal X \<in> P & y < real_of_preal X))"
by (blast dest!: bspec real_gt_zero_preal_Ex [THEN iffD1])

lemma real_sup_lemma2:
     "[| \<forall>x \<in> P. 0 < x;  a \<in> P;   \<forall>x \<in> P. x < y |]  
      ==> (\<exists>X. X\<in> {w. real_of_preal w \<in> P}) &  
          (\<exists>Y. \<forall>X\<in> {w. real_of_preal w \<in> P}. X < Y)"
apply (rule conjI)
apply (blast dest: bspec real_gt_zero_preal_Ex [THEN iffD1], auto)
apply (drule bspec, assumption)
apply (frule bspec, assumption)
apply (drule order_less_trans, assumption)
apply (drule real_gt_zero_preal_Ex [THEN iffD1], force) 
done

(*-------------------------------------------------------------
            Completeness of Positive Reals
 -------------------------------------------------------------*)

(**
 Supremum property for the set of positive reals
 FIXME: long proof - should be improved
**)

(*Let P be a non-empty set of positive reals, with an upper bound y.
  Then P has a least upper bound (written S).  
FIXME: Can the premise be weakened to \<forall>x \<in> P. x\<le> y ??*)
lemma posreal_complete: "[| \<forall>x \<in> P. (0::real) < x;  \<exists>x. x \<in> P;  \<exists>y. \<forall>x \<in> P. x<y |]  
      ==> (\<exists>S. \<forall>y. (\<exists>x \<in> P. y < x) = (y < S))"
apply (rule_tac x = "real_of_preal (psup ({w. real_of_preal w \<in> P}))" in exI)
apply clarify
apply (case_tac "0 < ya", auto)
apply (frule real_sup_lemma2, assumption+)
apply (drule real_gt_zero_preal_Ex [THEN iffD1])
apply (drule_tac [3] real_less_all_real2, auto)
apply (rule preal_complete [THEN iffD1])
apply (auto intro: order_less_imp_le)
apply (frule real_gt_preal_preal_Ex, force)
(* second part *)
apply (rule real_sup_lemma1 [THEN iffD2], assumption)
apply (auto dest!: real_less_all_real2 real_gt_zero_preal_Ex [THEN iffD1])
apply (frule_tac [2] real_sup_lemma2)
apply (frule real_sup_lemma2, assumption+, clarify) 
apply (rule preal_complete [THEN iffD2, THEN bexE])
prefer 3 apply blast
apply (blast intro!: order_less_imp_le)+
done

(*--------------------------------------------------------
   Completeness properties using isUb, isLub etc.
 -------------------------------------------------------*)

lemma real_isLub_unique: "[| isLub R S x; isLub R S y |] ==> x = (y::real)"
apply (frule isLub_isUb)
apply (frule_tac x = y in isLub_isUb)
apply (blast intro!: real_le_anti_sym dest!: isLub_le_isUb)
done

lemma real_order_restrict: "[| (x::real) <=* S'; S <= S' |] ==> x <=* S"
by (unfold setle_def setge_def, blast)

(*----------------------------------------------------------------
           Completeness theorem for the positive reals(again)
 ----------------------------------------------------------------*)

lemma posreals_complete:
     "[| \<forall>x \<in>S. 0 < x;  
         \<exists>x. x \<in>S;  
         \<exists>u. isUb (UNIV::real set) S u  
      |] ==> \<exists>t. isLub (UNIV::real set) S t"
apply (rule_tac x = "real_of_preal (psup ({w. real_of_preal w \<in> S}))" in exI)
apply (auto simp add: isLub_def leastP_def isUb_def)
apply (auto intro!: setleI setgeI dest!: real_gt_zero_preal_Ex [THEN iffD1])
apply (frule_tac x = y in bspec, assumption)
apply (drule real_gt_zero_preal_Ex [THEN iffD1])
apply (auto simp add: real_of_preal_le_iff)
apply (frule_tac y = "real_of_preal ya" in setleD, assumption)
apply (frule real_ge_preal_preal_Ex, safe)
apply (blast intro!: preal_psup_le dest!: setleD intro: real_of_preal_le_iff [THEN iffD1])
apply (frule_tac x = x in bspec, assumption)
apply (frule isUbD2)
apply (drule real_gt_zero_preal_Ex [THEN iffD1])
apply (auto dest!: isUbD real_ge_preal_preal_Ex simp add: real_of_preal_le_iff)
apply (blast dest!: setleD intro!: psup_le_ub intro: real_of_preal_le_iff [THEN iffD1])
done


(*-------------------------------
    Lemmas
 -------------------------------*)
lemma real_sup_lemma3: "\<forall>y \<in> {z. \<exists>x \<in> P. z = x + (-xa) + 1} Int {x. 0 < x}. 0 < y"
by auto
 
lemma lemma_le_swap2: "(xa <= S + X + (-Z)) = (xa + (-X) + Z <= (S::real))"
by auto

lemma lemma_real_complete2b: "[| (x::real) + (-X) + 1 <= S; xa <= x |] ==> xa <= S + X + (- 1)"
by arith

(*----------------------------------------------------------
      reals Completeness (again!)
 ----------------------------------------------------------*)
lemma reals_complete: "[| \<exists>X. X \<in>S;  \<exists>Y. isUb (UNIV::real set) S Y |]   
      ==> \<exists>t. isLub (UNIV :: real set) S t"
apply safe
apply (subgoal_tac "\<exists>u. u\<in> {z. \<exists>x \<in>S. z = x + (-X) + 1} Int {x. 0 < x}")
apply (subgoal_tac "isUb (UNIV::real set) ({z. \<exists>x \<in>S. z = x + (-X) + 1} Int {x. 0 < x}) (Y + (-X) + 1) ")
apply (cut_tac P = S and xa = X in real_sup_lemma3)
apply (frule posreals_complete [OF _ _ exI], blast, blast, safe)
apply (rule_tac x = "t + X + (- 1) " in exI)
apply (rule isLubI2)
apply (rule_tac [2] setgeI, safe)
apply (subgoal_tac [2] "isUb (UNIV:: real set) ({z. \<exists>x \<in>S. z = x + (-X) + 1} Int {x. 0 < x}) (y + (-X) + 1) ")
apply (drule_tac [2] y = " (y + (- X) + 1) " in isLub_le_isUb)
 prefer 2 apply assumption
 prefer 2
apply arith
apply (rule setleI [THEN isUbI], safe)
apply (rule_tac x = x and y = y in linorder_cases)
apply (subst lemma_le_swap2)
apply (frule isLubD2)
 prefer 2 apply assumption
apply safe
apply blast
apply arith
apply (subst lemma_le_swap2)
apply (frule isLubD2)
 prefer 2 apply assumption
apply blast
apply (rule lemma_real_complete2b)
apply (erule_tac [2] order_less_imp_le)
apply (blast intro!: isLubD2, blast) 
apply (simp (no_asm_use) add: real_add_assoc)
apply (blast dest: isUbD intro!: setleI [THEN isUbI] intro: add_right_mono)
apply (blast dest: isUbD intro!: setleI [THEN isUbI] intro: add_right_mono, auto)
done


subsection{*Corollary: the Archimedean Property of the Reals*}

lemma reals_Archimedean: "0 < x ==> \<exists>n. inverse (real(Suc n)) < x"
apply (rule ccontr)
apply (subgoal_tac "\<forall>n. x * real (Suc n) <= 1")
 prefer 2
apply (simp add: linorder_not_less inverse_eq_divide, clarify) 
apply (drule_tac x = n in spec)
apply (drule_tac c = "real (Suc n)"  in mult_right_mono)
apply (rule real_of_nat_ge_zero)
apply (simp add: real_of_nat_Suc_gt_zero [THEN real_not_refl2, THEN not_sym] real_mult_commute)
apply (subgoal_tac "isUb (UNIV::real set) {z. \<exists>n. z = x* (real (Suc n))} 1")
apply (subgoal_tac "\<exists>X. X \<in> {z. \<exists>n. z = x* (real (Suc n))}")
apply (drule reals_complete)
apply (auto intro: isUbI setleI)
apply (subgoal_tac "\<forall>m. x* (real (Suc m)) <= t")
apply (simp add: real_of_nat_Suc right_distrib)
prefer 2 apply (blast intro: isLubD2)
apply (simp add: le_diff_eq [symmetric] real_diff_def)
apply (subgoal_tac "isUb (UNIV::real set) {z. \<exists>n. z = x* (real (Suc n))} (t + (-x))")
prefer 2 apply (blast intro!: isUbI setleI)
apply (drule_tac y = "t+ (-x) " in isLub_le_isUb)
apply (auto simp add: real_of_nat_Suc right_distrib)
done

(*There must be other proofs, e.g. Suc of the largest integer in the
  cut representing x*)
lemma reals_Archimedean2: "\<exists>n. (x::real) < real (n::nat)"
apply (rule_tac x = x and y = 0 in linorder_cases)
apply (rule_tac x = 0 in exI)
apply (rule_tac [2] x = 1 in exI)
apply (auto elim: order_less_trans simp add: real_of_nat_one)
apply (frule positive_imp_inverse_positive [THEN reals_Archimedean], safe)
apply (rule_tac x = "Suc n" in exI)
apply (frule_tac b = "inverse x" in mult_strict_right_mono, auto)
done

lemma reals_Archimedean3: "0 < x ==> \<forall>y. \<exists>(n::nat). y < real n * x"
apply safe
apply (cut_tac x = "y*inverse (x) " in reals_Archimedean2)
apply safe
apply (frule_tac a = "y * inverse x" in mult_strict_right_mono)
apply (auto simp add: mult_assoc real_of_nat_def)
done

ML
{*
val real_sum_of_halves = thm "real_sum_of_halves";
val posreal_complete = thm "posreal_complete";
val real_isLub_unique = thm "real_isLub_unique";
val real_order_restrict = thm "real_order_restrict";
val posreals_complete = thm "posreals_complete";
val reals_complete = thm "reals_complete";
val reals_Archimedean = thm "reals_Archimedean";
val reals_Archimedean2 = thm "reals_Archimedean2";
val reals_Archimedean3 = thm "reals_Archimedean3";
*}

end




(*  Title       : RComplete.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
                  Converted to Isar and polished by lcp
                  Most floor and ceiling lemmas by Jeremy Avigad
    Copyright   : 1998  University of Cambridge
    Copyright   : 2001,2002  University of Edinburgh
*) 

header{*Completeness of the Reals; Floor and Ceiling Functions*}

theory RComplete
imports Lubs RealDef
begin

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
apply (blast intro!: order_antisym dest!: isLub_le_isUb)
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
apply (simp (no_asm_use) add: add_assoc)
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
apply (simp add: times_divide_eq_right real_of_nat_Suc_gt_zero [THEN real_not_refl2, THEN not_sym] mult_commute)
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

lemma reals_Archimedean6:
     "0 \<le> r ==> \<exists>(n::nat). real (n - 1) \<le> r & r < real (n)"
apply (insert reals_Archimedean2 [of r], safe)
apply (frule_tac P = "%k. r < real k" and k = n and m = "%x. x"
       in ex_has_least_nat, auto)
apply (rule_tac x = x in exI)
apply (case_tac x, simp)
apply (rename_tac x')
apply (drule_tac x = x' in spec, simp)
done

lemma reals_Archimedean6a: "0 \<le> r ==> \<exists>n. real (n) \<le> r & r < real (Suc n)"
by (drule reals_Archimedean6, auto)

lemma reals_Archimedean_6b_int:
     "0 \<le> r ==> \<exists>n::int. real n \<le> r & r < real (n+1)"
apply (drule reals_Archimedean6a, auto)
apply (rule_tac x = "int n" in exI)
apply (simp add: real_of_int_real_of_nat real_of_nat_Suc)
done

lemma reals_Archimedean_6c_int:
     "r < 0 ==> \<exists>n::int. real n \<le> r & r < real (n+1)"
apply (rule reals_Archimedean_6b_int [of "-r", THEN exE], simp, auto)
apply (rename_tac n)
apply (drule real_le_imp_less_or_eq, auto)
apply (rule_tac x = "- n - 1" in exI)
apply (rule_tac [2] x = "- n" in exI, auto)
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


subsection{*Floor and Ceiling Functions from the Reals to the Integers*}

constdefs

  floor :: "real => int"
   "floor r == (LEAST n::int. r < real (n+1))"

  ceiling :: "real => int"
    "ceiling r == - floor (- r)"

syntax (xsymbols)
  floor :: "real => int"     ("\<lfloor>_\<rfloor>")
  ceiling :: "real => int"   ("\<lceil>_\<rceil>")

syntax (HTML output)
  floor :: "real => int"     ("\<lfloor>_\<rfloor>")
  ceiling :: "real => int"   ("\<lceil>_\<rceil>")


lemma number_of_less_real_of_int_iff [simp]:
     "((number_of n) < real (m::int)) = (number_of n < m)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma number_of_less_real_of_int_iff2 [simp]:
     "(real (m::int) < (number_of n)) = (m < number_of n)"
apply auto
apply (rule real_of_int_less_iff [THEN iffD1])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD2], auto)
done

lemma number_of_le_real_of_int_iff [simp]:
     "((number_of n) \<le> real (m::int)) = (number_of n \<le> m)"
by (simp add: linorder_not_less [symmetric])

lemma number_of_le_real_of_int_iff2 [simp]:
     "(real (m::int) \<le> (number_of n)) = (m \<le> number_of n)"
by (simp add: linorder_not_less [symmetric])

lemma floor_zero [simp]: "floor 0 = 0"
apply (simp add: floor_def del: real_of_int_add)
apply (rule Least_equality)
apply simp_all
done

lemma floor_real_of_nat_zero [simp]: "floor (real (0::nat)) = 0"
by auto

lemma floor_real_of_nat [simp]: "floor (real (n::nat)) = int n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1])
apply (simp_all add: real_of_int_real_of_nat)
done

lemma floor_minus_real_of_nat [simp]: "floor (- real (n::nat)) = - int n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_minus [THEN sym, THEN subst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1])
apply (simp_all add: real_of_int_real_of_nat)
done

lemma floor_real_of_int [simp]: "floor (real (n::int)) = n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1], auto)
done

lemma floor_minus_real_of_int [simp]: "floor (- real (n::int)) = - n"
apply (simp only: floor_def)
apply (rule Least_equality)
apply (drule_tac [2] real_of_int_minus [THEN sym, THEN subst])
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1], auto)
done

lemma real_lb_ub_int: " \<exists>n::int. real n \<le> r & r < real (n+1)"
apply (case_tac "r < 0")
apply (blast intro: reals_Archimedean_6c_int)
apply (simp only: linorder_not_less)
apply (blast intro: reals_Archimedean_6b_int reals_Archimedean_6c_int)
done

lemma lemma_floor:
  assumes a1: "real m \<le> r" and a2: "r < real n + 1"
  shows "m \<le> (n::int)"
proof -
  have "real m < real n + 1" by (rule order_le_less_trans)
  also have "... = real(n+1)" by simp
  finally have "m < n+1" by (simp only: real_of_int_less_iff)
  thus ?thesis by arith
qed

lemma real_of_int_floor_le [simp]: "real (floor r) \<le> r"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of r], safe)
apply (rule theI2)
apply auto
apply (subst int_le_real_less, simp)
apply (drule_tac x = n in spec)
apply auto
apply (subgoal_tac "n <= x")
apply simp
apply (subst int_le_real_less, simp)
done

lemma floor_mono: "x < y ==> floor x \<le> floor y"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of x])
apply (insert real_lb_ub_int [of y], safe)
apply (rule theI2)
apply (rule_tac [3] theI2)
apply simp
apply (erule conjI)
apply (auto simp add: order_eq_iff int_le_real_less)
done

lemma floor_mono2: "x \<le> y ==> floor x \<le> floor y"
by (auto dest: real_le_imp_less_or_eq simp add: floor_mono)

lemma lemma_floor2: "real n < real (x::int) + 1 ==> n \<le> x"
by (auto intro: lemma_floor)

lemma real_of_int_floor_cancel [simp]:
    "(real (floor x) = x) = (\<exists>n::int. x = real n)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of x], erule exE)
apply (rule theI2)
apply (auto intro: lemma_floor) 
apply (auto simp add: order_eq_iff int_le_real_less)
done

lemma floor_eq: "[| real n < x; x < real n + 1 |] ==> floor x = n"
apply (simp add: floor_def)
apply (rule Least_equality)
apply (auto intro: lemma_floor)
done

lemma floor_eq2: "[| real n \<le> x; x < real n + 1 |] ==> floor x = n"
apply (simp add: floor_def)
apply (rule Least_equality)
apply (auto intro: lemma_floor)
done

lemma floor_eq3: "[| real n < x; x < real (Suc n) |] ==> nat(floor x) = n"
apply (rule inj_int [THEN injD])
apply (simp add: real_of_nat_Suc)
apply (simp add: real_of_nat_Suc floor_eq floor_eq [where n = "int n"])
done

lemma floor_eq4: "[| real n \<le> x; x < real (Suc n) |] ==> nat(floor x) = n"
apply (drule order_le_imp_less_or_eq)
apply (auto intro: floor_eq3)
done

lemma floor_number_of_eq [simp]:
     "floor(number_of n :: real) = (number_of n :: int)"
apply (subst real_number_of [symmetric])
apply (rule floor_real_of_int)
done

lemma floor_one [simp]: "floor 1 = 1"
  apply (rule trans)
  prefer 2
  apply (rule floor_real_of_int)
  apply simp
done

lemma real_of_int_floor_ge_diff_one [simp]: "r - 1 \<le> real(floor r)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of r], safe)
apply (rule theI2)
apply (auto intro: lemma_floor)
apply (auto simp add: order_eq_iff int_le_real_less)
done

lemma real_of_int_floor_gt_diff_one [simp]: "r - 1 < real(floor r)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of r], safe)
apply (rule theI2)
apply (auto intro: lemma_floor)
apply (auto simp add: order_eq_iff int_le_real_less)
done

lemma real_of_int_floor_add_one_ge [simp]: "r \<le> real(floor r) + 1"
apply (insert real_of_int_floor_ge_diff_one [of r])
apply (auto simp del: real_of_int_floor_ge_diff_one)
done

lemma real_of_int_floor_add_one_gt [simp]: "r < real(floor r) + 1"
apply (insert real_of_int_floor_gt_diff_one [of r])
apply (auto simp del: real_of_int_floor_gt_diff_one)
done

lemma le_floor: "real a <= x ==> a <= floor x"
  apply (subgoal_tac "a < floor x + 1")
  apply arith
  apply (subst real_of_int_less_iff [THEN sym])
  apply simp
  apply (insert real_of_int_floor_add_one_gt [of x]) 
  apply arith
done

lemma real_le_floor: "a <= floor x ==> real a <= x"
  apply (rule order_trans)
  prefer 2
  apply (rule real_of_int_floor_le)
  apply (subst real_of_int_le_iff)
  apply assumption
done

lemma le_floor_eq: "(a <= floor x) = (real a <= x)"
  apply (rule iffI)
  apply (erule real_le_floor)
  apply (erule le_floor)
done

lemma le_floor_eq_number_of [simp]: 
    "(number_of n <= floor x) = (number_of n <= x)"
by (simp add: le_floor_eq)

lemma le_floor_eq_zero [simp]: "(0 <= floor x) = (0 <= x)"
by (simp add: le_floor_eq)

lemma le_floor_eq_one [simp]: "(1 <= floor x) = (1 <= x)"
by (simp add: le_floor_eq)

lemma floor_less_eq: "(floor x < a) = (x < real a)"
  apply (subst linorder_not_le [THEN sym])+
  apply simp
  apply (rule le_floor_eq)
done

lemma floor_less_eq_number_of [simp]: 
    "(floor x < number_of n) = (x < number_of n)"
by (simp add: floor_less_eq)

lemma floor_less_eq_zero [simp]: "(floor x < 0) = (x < 0)"
by (simp add: floor_less_eq)

lemma floor_less_eq_one [simp]: "(floor x < 1) = (x < 1)"
by (simp add: floor_less_eq)

lemma less_floor_eq: "(a < floor x) = (real a + 1 <= x)"
  apply (insert le_floor_eq [of "a + 1" x])
  apply auto
done

lemma less_floor_eq_number_of [simp]: 
    "(number_of n < floor x) = (number_of n + 1 <= x)"
by (simp add: less_floor_eq)

lemma less_floor_eq_zero [simp]: "(0 < floor x) = (1 <= x)"
by (simp add: less_floor_eq)

lemma less_floor_eq_one [simp]: "(1 < floor x) = (2 <= x)"
by (simp add: less_floor_eq)

lemma floor_le_eq: "(floor x <= a) = (x < real a + 1)"
  apply (insert floor_less_eq [of x "a + 1"])
  apply auto
done

lemma floor_le_eq_number_of [simp]: 
    "(floor x <= number_of n) = (x < number_of n + 1)"
by (simp add: floor_le_eq)

lemma floor_le_eq_zero [simp]: "(floor x <= 0) = (x < 1)"
by (simp add: floor_le_eq)

lemma floor_le_eq_one [simp]: "(floor x <= 1) = (x < 2)"
by (simp add: floor_le_eq)

lemma floor_add [simp]: "floor (x + real a) = floor x + a"
  apply (subst order_eq_iff)
  apply (rule conjI)
  prefer 2
  apply (subgoal_tac "floor x + a < floor (x + real a) + 1")
  apply arith
  apply (subst real_of_int_less_iff [THEN sym])
  apply simp
  apply (subgoal_tac "x + real a < real(floor(x + real a)) + 1")
  apply (subgoal_tac "real (floor x) <= x")
  apply arith
  apply (rule real_of_int_floor_le)
  apply (rule real_of_int_floor_add_one_gt)
  apply (subgoal_tac "floor (x + real a) < floor x + a + 1")
  apply arith
  apply (subst real_of_int_less_iff [THEN sym])  
  apply simp
  apply (subgoal_tac "real(floor(x + real a)) <= x + real a") 
  apply (subgoal_tac "x < real(floor x) + 1")
  apply arith
  apply (rule real_of_int_floor_add_one_gt)
  apply (rule real_of_int_floor_le)
done

lemma floor_add_number_of [simp]: 
    "floor (x + number_of n) = floor x + number_of n"
  apply (subst floor_add [THEN sym])
  apply simp
done

lemma floor_add_one [simp]: "floor (x + 1) = floor x + 1"
  apply (subst floor_add [THEN sym])
  apply simp
done

lemma floor_subtract [simp]: "floor (x - real a) = floor x - a"
  apply (subst diff_minus)+
  apply (subst real_of_int_minus [THEN sym])
  apply (rule floor_add)
done

lemma floor_subtract_number_of [simp]: "floor (x - number_of n) = 
    floor x - number_of n"
  apply (subst floor_subtract [THEN sym])
  apply simp
done

lemma floor_subtract_one [simp]: "floor (x - 1) = floor x - 1"
  apply (subst floor_subtract [THEN sym])
  apply simp
done

lemma ceiling_zero [simp]: "ceiling 0 = 0"
by (simp add: ceiling_def)

lemma ceiling_real_of_nat [simp]: "ceiling (real (n::nat)) = int n"
by (simp add: ceiling_def)

lemma ceiling_real_of_nat_zero [simp]: "ceiling (real (0::nat)) = 0"
by auto

lemma ceiling_floor [simp]: "ceiling (real (floor r)) = floor r"
by (simp add: ceiling_def)

lemma floor_ceiling [simp]: "floor (real (ceiling r)) = ceiling r"
by (simp add: ceiling_def)

lemma real_of_int_ceiling_ge [simp]: "r \<le> real (ceiling r)"
apply (simp add: ceiling_def)
apply (subst le_minus_iff, simp)
done

lemma ceiling_mono: "x < y ==> ceiling x \<le> ceiling y"
by (simp add: floor_mono ceiling_def)

lemma ceiling_mono2: "x \<le> y ==> ceiling x \<le> ceiling y"
by (simp add: floor_mono2 ceiling_def)

lemma real_of_int_ceiling_cancel [simp]:
     "(real (ceiling x) = x) = (\<exists>n::int. x = real n)"
apply (auto simp add: ceiling_def)
apply (drule arg_cong [where f = uminus], auto)
apply (rule_tac x = "-n" in exI, auto)
done

lemma ceiling_eq: "[| real n < x; x < real n + 1 |] ==> ceiling x = n + 1"
apply (simp add: ceiling_def)
apply (rule minus_equation_iff [THEN iffD1])
apply (simp add: floor_eq [where n = "-(n+1)"])
done

lemma ceiling_eq2: "[| real n < x; x \<le> real n + 1 |] ==> ceiling x = n + 1"
by (simp add: ceiling_def floor_eq2 [where n = "-(n+1)"])

lemma ceiling_eq3: "[| real n - 1 < x; x \<le> real n  |] ==> ceiling x = n"
by (simp add: ceiling_def floor_eq2 [where n = "-n"])

lemma ceiling_real_of_int [simp]: "ceiling (real (n::int)) = n"
by (simp add: ceiling_def)

lemma ceiling_number_of_eq [simp]:
     "ceiling (number_of n :: real) = (number_of n)"
apply (subst real_number_of [symmetric])
apply (rule ceiling_real_of_int)
done

lemma ceiling_one [simp]: "ceiling 1 = 1"
  by (unfold ceiling_def, simp)

lemma real_of_int_ceiling_diff_one_le [simp]: "real (ceiling r) - 1 \<le> r"
apply (rule neg_le_iff_le [THEN iffD1])
apply (simp add: ceiling_def diff_minus)
done

lemma real_of_int_ceiling_le_add_one [simp]: "real (ceiling r) \<le> r + 1"
apply (insert real_of_int_ceiling_diff_one_le [of r])
apply (simp del: real_of_int_ceiling_diff_one_le)
done

lemma ceiling_le: "x <= real a ==> ceiling x <= a"
  apply (unfold ceiling_def)
  apply (subgoal_tac "-a <= floor(- x)")
  apply simp
  apply (rule le_floor)
  apply simp
done

lemma ceiling_le_real: "ceiling x <= a ==> x <= real a"
  apply (unfold ceiling_def)
  apply (subgoal_tac "real(- a) <= - x")
  apply simp
  apply (rule real_le_floor)
  apply simp
done

lemma ceiling_le_eq: "(ceiling x <= a) = (x <= real a)"
  apply (rule iffI)
  apply (erule ceiling_le_real)
  apply (erule ceiling_le)
done

lemma ceiling_le_eq_number_of [simp]: 
    "(ceiling x <= number_of n) = (x <= number_of n)"
by (simp add: ceiling_le_eq)

lemma ceiling_le_zero_eq [simp]: "(ceiling x <= 0) = (x <= 0)" 
by (simp add: ceiling_le_eq)

lemma ceiling_le_eq_one [simp]: "(ceiling x <= 1) = (x <= 1)" 
by (simp add: ceiling_le_eq)

lemma less_ceiling_eq: "(a < ceiling x) = (real a < x)"
  apply (subst linorder_not_le [THEN sym])+
  apply simp
  apply (rule ceiling_le_eq)
done

lemma less_ceiling_eq_number_of [simp]: 
    "(number_of n < ceiling x) = (number_of n < x)"
by (simp add: less_ceiling_eq)

lemma less_ceiling_eq_zero [simp]: "(0 < ceiling x) = (0 < x)"
by (simp add: less_ceiling_eq)

lemma less_ceiling_eq_one [simp]: "(1 < ceiling x) = (1 < x)"
by (simp add: less_ceiling_eq)

lemma ceiling_less_eq: "(ceiling x < a) = (x <= real a - 1)"
  apply (insert ceiling_le_eq [of x "a - 1"])
  apply auto
done

lemma ceiling_less_eq_number_of [simp]: 
    "(ceiling x < number_of n) = (x <= number_of n - 1)"
by (simp add: ceiling_less_eq)

lemma ceiling_less_eq_zero [simp]: "(ceiling x < 0) = (x <= -1)"
by (simp add: ceiling_less_eq)

lemma ceiling_less_eq_one [simp]: "(ceiling x < 1) = (x <= 0)"
by (simp add: ceiling_less_eq)

lemma le_ceiling_eq: "(a <= ceiling x) = (real a - 1 < x)"
  apply (insert less_ceiling_eq [of "a - 1" x])
  apply auto
done

lemma le_ceiling_eq_number_of [simp]: 
    "(number_of n <= ceiling x) = (number_of n - 1 < x)"
by (simp add: le_ceiling_eq)

lemma le_ceiling_eq_zero [simp]: "(0 <= ceiling x) = (-1 < x)"
by (simp add: le_ceiling_eq)

lemma le_ceiling_eq_one [simp]: "(1 <= ceiling x) = (0 < x)"
by (simp add: le_ceiling_eq)

lemma ceiling_add [simp]: "ceiling (x + real a) = ceiling x + a"
  apply (unfold ceiling_def, simp)
  apply (subst real_of_int_minus [THEN sym])
  apply (subst floor_add)
  apply simp
done

lemma ceiling_add_number_of [simp]: "ceiling (x + number_of n) = 
    ceiling x + number_of n"
  apply (subst ceiling_add [THEN sym])
  apply simp
done

lemma ceiling_add_one [simp]: "ceiling (x + 1) = ceiling x + 1"
  apply (subst ceiling_add [THEN sym])
  apply simp
done

lemma ceiling_subtract [simp]: "ceiling (x - real a) = ceiling x - a"
  apply (subst diff_minus)+
  apply (subst real_of_int_minus [THEN sym])
  apply (rule ceiling_add)
done

lemma ceiling_subtract_number_of [simp]: "ceiling (x - number_of n) = 
    ceiling x - number_of n"
  apply (subst ceiling_subtract [THEN sym])
  apply simp
done

lemma ceiling_subtract_one [simp]: "ceiling (x - 1) = ceiling x - 1"
  apply (subst ceiling_subtract [THEN sym])
  apply simp
done

subsection {* Versions for the natural numbers *}

constdefs
  natfloor :: "real => nat"
  "natfloor x == nat(floor x)"
  natceiling :: "real => nat"
  "natceiling x == nat(ceiling x)"

lemma natfloor_zero [simp]: "natfloor 0 = 0"
  by (unfold natfloor_def, simp)

lemma natfloor_one [simp]: "natfloor 1 = 1"
  by (unfold natfloor_def, simp)

lemma zero_le_natfloor [simp]: "0 <= natfloor x"
  by (unfold natfloor_def, simp)

lemma natfloor_number_of_eq [simp]: "natfloor (number_of n) = number_of n"
  by (unfold natfloor_def, simp)

lemma natfloor_real_of_nat [simp]: "natfloor(real n) = n"
  by (unfold natfloor_def, simp)

lemma real_natfloor_le: "0 <= x ==> real(natfloor x) <= x"
  by (unfold natfloor_def, simp)

lemma natfloor_neg: "x <= 0 ==> natfloor x = 0"
  apply (unfold natfloor_def)
  apply (subgoal_tac "floor x <= floor 0")
  apply simp
  apply (erule floor_mono2)
done

lemma natfloor_mono: "x <= y ==> natfloor x <= natfloor y"
  apply (case_tac "0 <= x")
  apply (subst natfloor_def)+
  apply (subst nat_le_eq_zle)
  apply force
  apply (erule floor_mono2) 
  apply (subst natfloor_neg)
  apply simp
  apply simp
done

lemma le_natfloor: "real x <= a ==> x <= natfloor a"
  apply (unfold natfloor_def)
  apply (subst nat_int [THEN sym])
  apply (subst nat_le_eq_zle)
  apply simp
  apply (rule le_floor)
  apply simp
done

lemma le_natfloor_eq: "0 <= x ==> (a <= natfloor x) = (real a <= x)"
  apply (rule iffI)
  apply (rule order_trans)
  prefer 2
  apply (erule real_natfloor_le)
  apply (subst real_of_nat_le_iff)
  apply assumption
  apply (erule le_natfloor)
done

lemma le_natfloor_eq_number_of [simp]: 
    "~ neg((number_of n)::int) ==> 0 <= x ==>
      (number_of n <= natfloor x) = (number_of n <= x)"
  apply (subst le_natfloor_eq, assumption)
  apply simp
done

lemma le_natfloor_one_eq [simp]: "(1 <= natfloor x) = (1 <= x)"
  apply (case_tac "0 <= x")
  apply (subst le_natfloor_eq, assumption, simp)
  apply (rule iffI)
  apply (subgoal_tac "natfloor x <= natfloor 0") 
  apply simp
  apply (rule natfloor_mono)
  apply simp
  apply simp
done

lemma natfloor_eq: "real n <= x ==> x < real n + 1 ==> natfloor x = n"
  apply (unfold natfloor_def)
  apply (subst nat_int [THEN sym]);back;
  apply (subst eq_nat_nat_iff)
  apply simp
  apply simp
  apply (rule floor_eq2)
  apply auto
done

lemma real_natfloor_add_one_gt: "x < real(natfloor x) + 1"
  apply (case_tac "0 <= x")
  apply (unfold natfloor_def)
  apply simp
  apply simp_all
done

lemma real_natfloor_gt_diff_one: "x - 1 < real(natfloor x)"
  apply (simp add: compare_rls)
  apply (rule real_natfloor_add_one_gt)
done

lemma ge_natfloor_plus_one_imp_gt: "natfloor z + 1 <= n ==> z < real n"
  apply (subgoal_tac "z < real(natfloor z) + 1")
  apply arith
  apply (rule real_natfloor_add_one_gt)
done

lemma natfloor_add [simp]: "0 <= x ==> natfloor (x + real a) = natfloor x + a"
  apply (unfold natfloor_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply (simp add: nat_add_distrib)
  apply simp
done

lemma natfloor_add_number_of [simp]: 
    "~neg ((number_of n)::int) ==> 0 <= x ==> 
      natfloor (x + number_of n) = natfloor x + number_of n"
  apply (subst natfloor_add [THEN sym])
  apply simp_all
done

lemma natfloor_add_one: "0 <= x ==> natfloor(x + 1) = natfloor x + 1"
  apply (subst natfloor_add [THEN sym])
  apply assumption
  apply simp
done

lemma natfloor_subtract [simp]: "real a <= x ==> 
    natfloor(x - real a) = natfloor x - a"
  apply (unfold natfloor_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply simp
  apply (subst nat_diff_distrib)
  apply simp
  apply (rule le_floor)
  apply simp_all
done

lemma natceiling_zero [simp]: "natceiling 0 = 0"
  by (unfold natceiling_def, simp)

lemma natceiling_one [simp]: "natceiling 1 = 1"
  by (unfold natceiling_def, simp)

lemma zero_le_natceiling [simp]: "0 <= natceiling x"
  by (unfold natceiling_def, simp)

lemma natceiling_number_of_eq [simp]: "natceiling (number_of n) = number_of n"
  by (unfold natceiling_def, simp)

lemma natceiling_real_of_nat [simp]: "natceiling(real n) = n"
  by (unfold natceiling_def, simp)

lemma real_natceiling_ge: "x <= real(natceiling x)"
  apply (unfold natceiling_def)
  apply (case_tac "x < 0")
  apply simp
  apply (subst real_nat_eq_real)
  apply (subgoal_tac "ceiling 0 <= ceiling x")
  apply simp
  apply (rule ceiling_mono2)
  apply simp
  apply simp
done

lemma natceiling_neg: "x <= 0 ==> natceiling x = 0"
  apply (unfold natceiling_def)
  apply simp
done

lemma natceiling_mono: "x <= y ==> natceiling x <= natceiling y"
  apply (case_tac "0 <= x")
  apply (subst natceiling_def)+
  apply (subst nat_le_eq_zle)
  apply (rule disjI2)
  apply (subgoal_tac "real (0::int) <= real(ceiling y)")
  apply simp
  apply (rule order_trans)
  apply simp
  apply (erule order_trans)
  apply simp
  apply (erule ceiling_mono2)
  apply (subst natceiling_neg)
  apply simp_all
done

lemma natceiling_le: "x <= real a ==> natceiling x <= a"
  apply (unfold natceiling_def)
  apply (case_tac "x < 0")
  apply simp
  apply (subst nat_int [THEN sym]);back;
  apply (subst nat_le_eq_zle)
  apply simp
  apply (rule ceiling_le)
  apply simp
done

lemma natceiling_le_eq: "0 <= x ==> (natceiling x <= a) = (x <= real a)"
  apply (rule iffI)
  apply (rule order_trans)
  apply (rule real_natceiling_ge)
  apply (subst real_of_nat_le_iff)
  apply assumption
  apply (erule natceiling_le)
done

lemma natceiling_le_eq2 [simp]: "~ neg((number_of n)::int) ==> 0 <= x ==>
    (natceiling x <= number_of n) = (x <= number_of n)"
  apply (subst natceiling_le_eq, assumption)
  apply simp
done

lemma natceiling_one_le_eq: "(natceiling x <= 1) = (x <= 1)"
  apply (case_tac "0 <= x")
  apply (subst natceiling_le_eq)
  apply assumption
  apply simp
  apply (subst natceiling_neg)
  apply simp
  apply simp
done

lemma natceiling_eq: "real n < x ==> x <= real n + 1 ==> natceiling x = n + 1"
  apply (unfold natceiling_def)
  apply (subst nat_int [THEN sym]);back;
  apply (subgoal_tac "nat(int n) + 1 = nat(int n + 1)")
  apply (erule ssubst)
  apply (subst eq_nat_nat_iff)
  apply (subgoal_tac "ceiling 0 <= ceiling x")
  apply simp
  apply (rule ceiling_mono2)
  apply force
  apply force
  apply (rule ceiling_eq2)
  apply (simp, simp)
  apply (subst nat_add_distrib)
  apply auto
done

lemma natceiling_add [simp]: "0 <= x ==> 
    natceiling (x + real a) = natceiling x + a"
  apply (unfold natceiling_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply simp
  apply (subst nat_add_distrib)
  apply (subgoal_tac "0 = ceiling 0")
  apply (erule ssubst)
  apply (erule ceiling_mono2)
  apply simp_all
done

lemma natceiling_add2 [simp]: "~ neg ((number_of n)::int) ==> 0 <= x ==> 
    natceiling (x + number_of n) = natceiling x + number_of n"
  apply (subst natceiling_add [THEN sym])
  apply simp_all
done

lemma natceiling_add_one: "0 <= x ==> natceiling(x + 1) = natceiling x + 1"
  apply (subst natceiling_add [THEN sym])
  apply assumption
  apply simp
done

lemma natceiling_subtract [simp]: "real a <= x ==> 
    natceiling(x - real a) = natceiling x - a"
  apply (unfold natceiling_def)
  apply (subgoal_tac "real a = real (int a)")
  apply (erule ssubst)
  apply simp
  apply (subst nat_diff_distrib)
  apply simp
  apply (rule order_trans)
  prefer 2
  apply (rule ceiling_mono2)
  apply assumption
  apply simp_all
done

lemma natfloor_div_nat: "1 <= x ==> 0 < y ==> 
  natfloor (x / real y) = natfloor x div y"
proof -
  assume "1 <= (x::real)" and "0 < (y::nat)"
  have "natfloor x = (natfloor x) div y * y + (natfloor x) mod y"
    by simp
  then have a: "real(natfloor x) = real ((natfloor x) div y) * real y + 
    real((natfloor x) mod y)"
    by (simp only: real_of_nat_add [THEN sym] real_of_nat_mult [THEN sym])
  have "x = real(natfloor x) + (x - real(natfloor x))"
    by simp
  then have "x = real ((natfloor x) div y) * real y + 
      real((natfloor x) mod y) + (x - real(natfloor x))"
    by (simp add: a)
  then have "x / real y = ... / real y"
    by simp
  also have "... = real((natfloor x) div y) + real((natfloor x) mod y) / 
    real y + (x - real(natfloor x)) / real y"
    by (auto simp add: ring_distrib ring_eq_simps add_divide_distrib
      diff_divide_distrib prems)
  finally have "natfloor (x / real y) = natfloor(...)" by simp
  also have "... = natfloor(real((natfloor x) mod y) / 
    real y + (x - real(natfloor x)) / real y + real((natfloor x) div y))"
    by (simp add: add_ac)
  also have "... = natfloor(real((natfloor x) mod y) / 
    real y + (x - real(natfloor x)) / real y) + (natfloor x) div y"
    apply (rule natfloor_add)
    apply (rule add_nonneg_nonneg)
    apply (rule divide_nonneg_pos)
    apply simp
    apply (simp add: prems)
    apply (rule divide_nonneg_pos)
    apply (simp add: compare_rls)
    apply (rule real_natfloor_le)
    apply (insert prems, auto)
    done
  also have "natfloor(real((natfloor x) mod y) / 
    real y + (x - real(natfloor x)) / real y) = 0"
    apply (rule natfloor_eq)
    apply simp
    apply (rule add_nonneg_nonneg)
    apply (rule divide_nonneg_pos)
    apply force
    apply (force simp add: prems)
    apply (rule divide_nonneg_pos)
    apply (simp add: compare_rls)
    apply (rule real_natfloor_le)
    apply (auto simp add: prems)
    apply (insert prems, arith)
    apply (simp add: add_divide_distrib [THEN sym])
    apply (subgoal_tac "real y = real y - 1 + 1")
    apply (erule ssubst)
    apply (rule add_le_less_mono)
    apply (simp add: compare_rls)
    apply (subgoal_tac "real(natfloor x mod y) + 1 = 
      real(natfloor x mod y + 1)")
    apply (erule ssubst)
    apply (subst real_of_nat_le_iff)
    apply (subgoal_tac "natfloor x mod y < y")
    apply arith
    apply (rule mod_less_divisor)
    apply assumption
    apply auto
    apply (simp add: compare_rls)
    apply (subst add_commute)
    apply (rule real_natfloor_add_one_gt)
    done
  finally show ?thesis
    by simp
qed

ML
{*
val number_of_less_real_of_int_iff = thm "number_of_less_real_of_int_iff";
val number_of_less_real_of_int_iff2 = thm "number_of_less_real_of_int_iff2";
val number_of_le_real_of_int_iff = thm "number_of_le_real_of_int_iff";
val number_of_le_real_of_int_iff2 = thm "number_of_le_real_of_int_iff2";
val floor_zero = thm "floor_zero";
val floor_real_of_nat_zero = thm "floor_real_of_nat_zero";
val floor_real_of_nat = thm "floor_real_of_nat";
val floor_minus_real_of_nat = thm "floor_minus_real_of_nat";
val floor_real_of_int = thm "floor_real_of_int";
val floor_minus_real_of_int = thm "floor_minus_real_of_int";
val reals_Archimedean6 = thm "reals_Archimedean6";
val reals_Archimedean6a = thm "reals_Archimedean6a";
val reals_Archimedean_6b_int = thm "reals_Archimedean_6b_int";
val reals_Archimedean_6c_int = thm "reals_Archimedean_6c_int";
val real_lb_ub_int = thm "real_lb_ub_int";
val lemma_floor = thm "lemma_floor";
val real_of_int_floor_le = thm "real_of_int_floor_le";
(*val floor_le = thm "floor_le";
val floor_le2 = thm "floor_le2";
*)
val lemma_floor2 = thm "lemma_floor2";
val real_of_int_floor_cancel = thm "real_of_int_floor_cancel";
val floor_eq = thm "floor_eq";
val floor_eq2 = thm "floor_eq2";
val floor_eq3 = thm "floor_eq3";
val floor_eq4 = thm "floor_eq4";
val floor_number_of_eq = thm "floor_number_of_eq";
val real_of_int_floor_ge_diff_one = thm "real_of_int_floor_ge_diff_one";
val real_of_int_floor_add_one_ge = thm "real_of_int_floor_add_one_ge";
val ceiling_zero = thm "ceiling_zero";
val ceiling_real_of_nat = thm "ceiling_real_of_nat";
val ceiling_real_of_nat_zero = thm "ceiling_real_of_nat_zero";
val ceiling_floor = thm "ceiling_floor";
val floor_ceiling = thm "floor_ceiling";
val real_of_int_ceiling_ge = thm "real_of_int_ceiling_ge";
(*
val ceiling_le = thm "ceiling_le";
val ceiling_le2 = thm "ceiling_le2";
*)
val real_of_int_ceiling_cancel = thm "real_of_int_ceiling_cancel";
val ceiling_eq = thm "ceiling_eq";
val ceiling_eq2 = thm "ceiling_eq2";
val ceiling_eq3 = thm "ceiling_eq3";
val ceiling_real_of_int = thm "ceiling_real_of_int";
val ceiling_number_of_eq = thm "ceiling_number_of_eq";
val real_of_int_ceiling_diff_one_le = thm "real_of_int_ceiling_diff_one_le";
val real_of_int_ceiling_le_add_one = thm "real_of_int_ceiling_le_add_one";
*}


end

(*  Title       : RComplete.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Copyright   : 2001,2002  University of Edinburgh
Converted to Isar and polished by lcp
*) 

header{*Completeness of the Reals; Floor and Ceiling Functions*}

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
apply (simp add: floor_def)
apply (rule Least_equality, auto)
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
apply (drule_tac [2] real_of_int_minus [THEN subst])
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
apply (drule_tac [2] real_of_int_minus [THEN subst])
apply (drule_tac [2] real_of_int_real_of_nat [THEN ssubst])
apply (drule_tac [2] real_of_int_less_iff [THEN iffD1], auto)
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
apply (rule theI2, auto)
done

lemma floor_le: "x < y ==> floor x \<le> floor y"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of x])
apply (insert real_lb_ub_int [of y], safe)
apply (rule theI2)
apply (rule_tac [3] theI2, auto)
done

lemma floor_le2: "x \<le> y ==> floor x \<le> floor y"
by (auto dest: real_le_imp_less_or_eq simp add: floor_le)

lemma lemma_floor2: "real n < real (x::int) + 1 ==> n \<le> x"
by (auto intro: lemma_floor)

lemma real_of_int_floor_cancel [simp]:
    "(real (floor x) = x) = (\<exists>n::int. x = real n)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of x], erule exE)
apply (rule theI2)
apply (auto intro: lemma_floor)
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
apply (simp add: real_of_nat_Suc floor_eq floor_eq [where n = "of_nat n"])
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

lemma real_of_int_floor_ge_diff_one [simp]: "r - 1 \<le> real(floor r)"
apply (simp add: floor_def Least_def)
apply (insert real_lb_ub_int [of r], safe)
apply (rule theI2)
apply (auto intro: lemma_floor)
done

lemma real_of_int_floor_add_one_ge [simp]: "r \<le> real(floor r) + 1"
apply (insert real_of_int_floor_ge_diff_one [of r])
apply (auto simp del: real_of_int_floor_ge_diff_one)
done


subsection{*Ceiling Function for Positive Reals*}

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

lemma ceiling_le: "x < y ==> ceiling x \<le> ceiling y"
by (simp add: floor_le ceiling_def)

lemma ceiling_le2: "x \<le> y ==> ceiling x \<le> ceiling y"
by (simp add: floor_le2 ceiling_def)

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

lemma real_of_int_ceiling_diff_one_le [simp]: "real (ceiling r) - 1 \<le> r"
apply (rule neg_le_iff_le [THEN iffD1])
apply (simp add: ceiling_def diff_minus)
done

lemma real_of_int_ceiling_le_add_one [simp]: "real (ceiling r) \<le> r + 1"
apply (insert real_of_int_ceiling_diff_one_le [of r])
apply (simp del: real_of_int_ceiling_diff_one_le)
done

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
val floor_le = thm "floor_le";
val floor_le2 = thm "floor_le2";
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
val ceiling_le = thm "ceiling_le";
val ceiling_le2 = thm "ceiling_le2";
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





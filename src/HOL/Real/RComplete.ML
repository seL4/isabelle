(*  Title       : HOL/Real/RComplete.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Completeness theorems for positive reals and reals.
*) 

Goal "x/2 + x/2 = (x::real)";
by (Simp_tac 1);
qed "real_sum_of_halves";

(*---------------------------------------------------------
       Completeness of reals: use supremum property of 
       preal and theorems about real_preal. Theorems 
       previously in Real.ML. 
 ---------------------------------------------------------*)
 (*a few lemmas*)
Goal "ALL x:P. 0 < x ==> \ 
\       ((EX x:P. y < x) = (EX X. real_of_preal X : P & \
\                          y < real_of_preal X))";
by (blast_tac (claset() addSDs [bspec, 
		    real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_sup_lemma1";

Goal "[| ALL x:P. 0 < x;  a: P;   ALL x: P. x < y |] \
\         ==> (EX X. X: {w. real_of_preal w : P}) & \
\             (EX Y. ALL X: {w. real_of_preal w : P}. X < Y)";
by (rtac conjI 1);
by (blast_tac (claset() addDs [bspec, 
                real_gt_zero_preal_Ex RS iffD1]) 1);
by Auto_tac;
by (dtac bspec 1 THEN assume_tac 1);
by (ftac bspec 1  THEN assume_tac 1);
by (dtac order_less_trans 1 THEN assume_tac 1); 
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (Force_tac 1);     
qed "real_sup_lemma2";

(*-------------------------------------------------------------
            Completeness of Positive Reals
 -------------------------------------------------------------*)

(**
 Supremum property for the set of positive reals
 FIXME: long proof - should be improved
**)

(*Let P be a non-empty set of positive reals, with an upper bound y.
  Then P has a least upper bound (written S).*)
Goal "[| ALL x:P. (0::real) < x;  EX x. x: P;  EX y. ALL x: P. x<y |] \
\     ==> (EX S. ALL y. (EX x: P. y < x) = (y < S))";
by (res_inst_tac 
   [("x","real_of_preal (psup({w. real_of_preal w : P}))")] exI 1);
by (Clarify_tac 1); 
by (case_tac "0 < ya" 1);
by Auto_tac; 
by (ftac real_sup_lemma2 1 THEN REPEAT (assume_tac 1));
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (dtac (real_less_all_real2) 3);
by Auto_tac;
by (rtac (preal_complete RS spec RS iffD1) 1);
by Auto_tac;
by (ftac real_gt_preal_preal_Ex 1);
by (Force_tac 1);   
(* second part *)
by (rtac (real_sup_lemma1 RS iffD2) 1 THEN assume_tac 1);
by (auto_tac (claset() addSDs [real_less_all_real2,
                               real_gt_zero_preal_Ex RS iffD1],
	      simpset()));
by (ftac real_sup_lemma2 2 THEN REPEAT (assume_tac 1));
by (ftac real_sup_lemma2 1 THEN REPEAT (assume_tac 1));
by (rtac (preal_complete RS spec RS iffD2 RS bexE) 1);
by (Blast_tac 3);
by (ALLGOALS(Blast_tac));
qed "posreal_complete";

(*--------------------------------------------------------
   Completeness properties using isUb, isLub etc.
 -------------------------------------------------------*)

Goal "[| isLub R S x; isLub R S y |] ==> x = (y::real)";
by (ftac isLub_isUb 1);
by (forw_inst_tac [("x","y")] isLub_isUb 1);
by (blast_tac (claset() addSIs [real_le_anti_sym]
                        addSDs [isLub_le_isUb]) 1);
qed "real_isLub_unique";

Goalw [setle_def,setge_def] "[| (x::real) <=* S'; S <= S' |] ==> x <=* S";
by (Blast_tac 1);
qed "real_order_restrict";

(*----------------------------------------------------------------
           Completeness theorem for the positive reals(again)
 ----------------------------------------------------------------*)

Goal "[| ALL x: S. 0 < x; \
\        EX x. x: S; \
\        EX u. isUb (UNIV::real set) S u \
\     |] ==> EX t. isLub (UNIV::real set) S t";
by (res_inst_tac 
    [("x","real_of_preal(psup({w. real_of_preal w : S}))")] exI 1);
by (auto_tac (claset(), simpset() addsimps 
    [isLub_def,leastP_def,isUb_def]));
by (auto_tac (claset() addSIs [setleI,setgeI] 
	         addSDs [(real_gt_zero_preal_Ex) RS iffD1],
	      simpset()));
by (forw_inst_tac [("x","y")] bspec 1 THEN assume_tac 1);
by (dtac ((real_gt_zero_preal_Ex) RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [real_of_preal_le_iff]));
by (rtac preal_psup_leI2a 1);
by (forw_inst_tac [("y","real_of_preal ya")] setleD 1 THEN assume_tac 1);
by (ftac real_ge_preal_preal_Ex 1);
by (Step_tac 1);
by (res_inst_tac [("x","y")] exI 1);
by (blast_tac (claset() addSDs [setleD] addIs [real_of_preal_le_iff RS iffD1]) 1);
by (forw_inst_tac [("x","x")] bspec 1 THEN assume_tac 1);
by (ftac isUbD2 1);
by (dtac ((real_gt_zero_preal_Ex) RS iffD1) 1);
by (auto_tac (claset() addSDs [isUbD, real_ge_preal_preal_Ex],
	      simpset() addsimps [real_of_preal_le_iff]));
by (blast_tac (claset() addSDs [setleD] addSIs [psup_le_ub1] 
	                addIs [real_of_preal_le_iff RS iffD1]) 1);
qed "posreals_complete";


(*-------------------------------
    Lemmas
 -------------------------------*)
Goal "ALL y : {z. EX x: P. z = x + (-xa) + 1} Int {x. 0 < x}. 0 < y";
by Auto_tac;
qed "real_sup_lemma3";
 
Goal "(xa <= S + X + (-Z)) = (xa + (-X) + Z <= (S::real))";
by Auto_tac;
qed "lemma_le_swap2";

Goal "[| (x::real) + (-X) + 1 <= S; xa <= x |] ==> xa <= S + X + (- 1)";
by (arith_tac 1);
by Auto_tac;
qed "lemma_real_complete2b";

(*----------------------------------------------------------
      reals Completeness (again!)
 ----------------------------------------------------------*)
Goal "[| EX X. X: S;  EX Y. isUb (UNIV::real set) S Y |]  \
\     ==> EX t. isLub (UNIV :: real set) S t";
by (Step_tac 1);
by (subgoal_tac "EX u. u: {z. EX x: S. z = x + (-X) + 1} \
\                Int {x. 0 < x}" 1);
by (subgoal_tac "isUb (UNIV::real set) ({z. EX x: S. z = x + (-X) + 1} \
\                Int {x. 0 < x})  (Y + (-X) + 1)" 1); 
by (cut_inst_tac [("P","S"),("xa","X")] real_sup_lemma3 1);
by (EVERY1[forward_tac [exI RSN (3,posreals_complete)], Blast_tac, Blast_tac, 
	   Step_tac]);
by (res_inst_tac [("x","t + X + (- 1)")] exI 1);
by (rtac isLubI2 1);
by (rtac setgeI 2 THEN Step_tac 2);
by (subgoal_tac "isUb (UNIV:: real set) ({z. EX x: S. z = x + (-X) + 1} \
\                Int {x. 0 < x})  (y + (-X) + 1)" 2); 
by (dres_inst_tac [("y","(y + (- X) + 1)")] isLub_le_isUb 2 
      THEN assume_tac 2);
by (full_simp_tac
    (simpset() addsimps [real_diff_def, real_diff_le_eq RS sym] @
                        real_add_ac) 2);
by (rtac (setleI RS isUbI) 1);
by (Step_tac 1);
by (res_inst_tac [("R1.0","x"),("R2.0","y")] real_linear_less2 1);
by (stac lemma_le_swap2 1);
by (ftac isLubD2 1 THEN assume_tac 2);
by (Step_tac 1);
by (Blast_tac 1);
by (arith_tac 1);
by (stac lemma_le_swap2 1);
by (ftac isLubD2 1 THEN assume_tac 2);
by (Blast_tac 1);
by (rtac lemma_real_complete2b 1);
by (etac order_less_imp_le 2);
by (blast_tac (claset() addSIs [isLubD2]) 1 THEN Step_tac 1);
by (full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (blast_tac (claset() addDs [isUbD] addSIs [setleI RS isUbI]
                        addIs [real_add_le_mono1]) 1);
by (blast_tac (claset() addDs [isUbD] addSIs [setleI RS isUbI]
                        addIs [real_add_le_mono1]) 1);
by (Auto_tac);
qed "reals_complete";

(*----------------------------------------------------------------
        Related: Archimedean property of reals
 ----------------------------------------------------------------*)

Goal "0 < real (Suc n)";
by (res_inst_tac [("y","real n")] order_le_less_trans 1); 
by (rtac (real_of_nat_ge_zero) 1);
by (simp_tac (simpset() addsimps [real_of_nat_Suc]) 1); 
qed "real_of_nat_Suc_gt_zero";

Goal "0 < x ==> EX n. inverse (real(Suc n)) < x";
by (rtac ccontr 1);
by (subgoal_tac "ALL n. x * real (Suc n) <= 1" 1);
by (asm_full_simp_tac
    (simpset() addsimps [linorder_not_less, real_inverse_eq_divide]) 2); 
by (Clarify_tac 2);
by (dres_inst_tac [("x","n")] spec 2); 
by (dres_inst_tac [("k","real (Suc n)")] (real_mult_le_mono1) 2); 
by (rtac real_of_nat_ge_zero 2);
by (asm_full_simp_tac (simpset()  
	 addsimps [real_of_nat_Suc_gt_zero RS real_not_refl2 RS not_sym, 
                   real_mult_commute]) 2); 
by (subgoal_tac "isUb (UNIV::real set) \
\                     {z. EX n. z = x*(real (Suc n))} 1" 1);
by (subgoal_tac "EX X. X : {z. EX n. z = x*(real (Suc n))}" 1);
by (dtac reals_complete 1);
by (auto_tac (claset() addIs [isUbI,setleI],simpset()));
by (subgoal_tac "ALL m. x*(real(Suc m)) <= t" 1);
by (asm_full_simp_tac (simpset() addsimps 
                       [real_of_nat_Suc, real_add_mult_distrib2]) 1);
by (blast_tac (claset() addIs [isLubD2]) 2);
by (asm_full_simp_tac
    (simpset() addsimps [real_le_diff_eq RS sym, real_diff_def]) 1);
by (subgoal_tac "isUb (UNIV::real set) \
\                  {z. EX n. z = x*(real (Suc n))} (t + (-x))" 1);
by (blast_tac (claset() addSIs [isUbI,setleI]) 2);
by (dres_inst_tac [("y","t+(-x)")] isLub_le_isUb 1);
by (auto_tac (claset(), 
	      simpset() addsimps [real_of_nat_Suc,real_add_mult_distrib2]));
qed "reals_Archimedean";

(*There must be other proofs, e.g. Suc of the largest integer in the
  cut representing x*)
Goal "EX n. (x::real) < real (n::nat)";
by (res_inst_tac [("R1.0","x"),("R2.0","0")] real_linear_less2 1);
by (res_inst_tac [("x","0")] exI 1);
by (res_inst_tac [("x","1")] exI 2);
by (auto_tac (claset() addEs [order_less_trans],
	      simpset() addsimps [real_of_nat_one]));
by (ftac (real_inverse_gt_0 RS reals_Archimedean) 1);
by (Step_tac 1 THEN res_inst_tac [("x","Suc n")] exI 1);
by (forw_inst_tac [("y","inverse x")] real_mult_less_mono1 1);
by Auto_tac;  
by (rtac (thm "less_imp_inverse_less") 1); 
by (assume_tac 1); 
by (assume_tac 1); 
qed "reals_Archimedean2";

Goal "0 < x ==> ALL y. EX (n::nat). y < real n * x";
by (Step_tac 1);
by (cut_inst_tac [("x","y*inverse(x)")] reals_Archimedean2 1);
by (Step_tac 1);
by (forw_inst_tac [("x","y * inverse x")] (real_mult_less_mono1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc,real_of_nat_def]));
qed "reals_Archimedean3";

